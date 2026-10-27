#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
VMF -> P2C конвертер (Portal 2 Puzzle Maker)

Как работает:
  1. Читает VMF и собирает выпуклые браши (world + func_detail).
  2. Превращает их в воксельную сетку (1 воксель = 128 юнитов по умолчанию).
  3. (опц.) Заливкой от info_player_start закрашивает всё, что вне комнаты.
  4. Пишет .p2c: метаданные, воксели, двери входа/выхода.

Запуск с окном:   python vmf2p2c.py
Запуск из консоли: python vmf2p2c.py карта.vmf результат.p2c [юнитов_на_воксель]
"""

import math
import os
import queue
import re
import sys
import threading
import time
from collections import deque

EPS = 0.01

# --------------------------------------------------------------------------
#  Парсер KeyValues (формат VMF)
# --------------------------------------------------------------------------
_TOKEN = re.compile(r'//[^\n]*|"((?:[^"\\]|\\.)*)"|([{}])|([^\s{}"]+)')
_NUM = re.compile(r'-?\d+(?:\.\d+)?(?:[eE][-+]?\d+)?')


class Node:
    __slots__ = ("name", "props", "children")

    def __init__(self, name):
        self.name = name
        self.props = {}
        self.children = []


def parse_kv(text):
    toks = []
    for m in _TOKEN.finditer(text):
        if m.group(1) is not None:
            toks.append(("s", m.group(1)))
        elif m.group(2):
            toks.append((m.group(2), m.group(2)))
        elif m.group(3) is not None:
            toks.append(("s", m.group(3)))
    root = Node("root")
    stack = [root]
    i, n = 0, len(toks)
    while i < n:
        kind, val = toks[i]
        if kind == "}":
            if len(stack) > 1:
                stack.pop()
            i += 1
        elif kind == "{":
            i += 1
        elif i + 1 < n and toks[i + 1][0] == "{":
            node = Node(val.lower())
            stack[-1].children.append(node)
            stack.append(node)
            i += 2
        elif i + 1 < n and toks[i + 1][0] == "s":
            stack[-1].props[val] = toks[i + 1][1]
            i += 2
        else:
            i += 1
    return root


# --------------------------------------------------------------------------
#  Браши
# --------------------------------------------------------------------------
def _sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def _cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def _dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


class Brush:
    __slots__ = ("planes", "bmin", "bmax", "black")


def build_brush(solid, skip_tools=True):
    raw, mats, pts = [], [], []
    for s in solid.children:
        if s.name != "side":
            continue
        nums = [float(x) for x in _NUM.findall(s.props.get("plane", ""))]
        if len(nums) < 9:
            continue
        p1, p2, p3 = tuple(nums[0:3]), tuple(nums[3:6]), tuple(nums[6:9])
        raw.append((p1, p2, p3))
        pts += [p1, p2, p3]
        mats.append(s.props.get("material", "").upper())
    if len(raw) < 4:
        return None
    if skip_tools and all(m.startswith("TOOLS/") for m in mats):
        return None

    c = (sum(p[0] for p in pts) / len(pts),
         sum(p[1] for p in pts) / len(pts),
         sum(p[2] for p in pts) / len(pts))

    planes = []
    for p1, p2, p3 in raw:
        n = _cross(_sub(p3, p1), _sub(p2, p1))
        ln = math.sqrt(_dot(n, n))
        if ln < 1e-9:
            continue
        n = (n[0] / ln, n[1] / ln, n[2] / ln)
        d = _dot(n, p1)
        if _dot(n, c) - d > 0:          # нормаль должна смотреть наружу
            n = (-n[0], -n[1], -n[2])
            d = -d
        planes.append((n[0], n[1], n[2], d))
    if len(planes) < 4:
        return None

    # вершины = пересечения троек плоскостей, лежащие внутри браша
    verts = []
    m = len(planes)
    for i in range(m):
        n1 = planes[i]
        for j in range(i + 1, m):
            n2 = planes[j]
            c23_base = n2
            for k in range(j + 1, m):
                n3 = planes[k]
                a, b, cc = n1[:3], n2[:3], n3[:3]
                bc = _cross(b, cc)
                det = _dot(a, bc)
                if abs(det) < 1e-9:
                    continue
                ca = _cross(cc, a)
                ab = _cross(a, b)
                x = (n1[3] * bc[0] + n2[3] * ca[0] + n3[3] * ab[0]) / det
                y = (n1[3] * bc[1] + n2[3] * ca[1] + n3[3] * ab[1]) / det
                z = (n1[3] * bc[2] + n2[3] * ca[2] + n3[3] * ab[2]) / det
                ok = True
                for p in planes:
                    if p[0] * x + p[1] * y + p[2] * z > p[3] + 0.05:
                        ok = False
                        break
                if ok:
                    verts.append((x, y, z))
    if not verts:
        return None

    br = Brush()
    br.planes = planes
    br.bmin = (min(v[0] for v in verts), min(v[1] for v in verts), min(v[2] for v in verts))
    br.bmax = (max(v[0] for v in verts), max(v[1] for v in verts), max(v[2] for v in verts))
    nb = sum(1 for mt in mats if "BLACK" in mt or "NOPORTAL" in mt)
    nw = sum(1 for mt in mats if "WHITE" in mt)
    br.black = nb > nw
    return br


def popcount(x):
    return bin(x).count("1")


# --------------------------------------------------------------------------
#  Конвертация
# --------------------------------------------------------------------------
def _origin(ent):
    nums = [float(x) for x in _NUM.findall(ent.props.get("origin", ""))]
    return tuple(nums[:3]) if len(nums) >= 3 else None


def _q(s):
    return str(s).replace("\\", "\\\\").replace('"', '\\"')


def convert(vmf_path, out_path, opt, log=print, progress=lambda f: None):
    unit = float(opt.get("unit", 128))
    s = int(opt.get("samples", 4))
    thr = float(opt.get("threshold", 25)) / 100.0
    need_bits = max(1, int(math.ceil(thr * s ** 3 - 1e-9)))
    full_mask = (1 << (s ** 3)) - 1
    offs = [(k + 0.5) / s * unit for k in range(s)]

    log("Читаю VMF: %s" % vmf_path)
    with open(vmf_path, "r", encoding="utf-8", errors="replace") as f:
        root = parse_kv(f.read())

    world = [n for n in root.children if n.name == "world"]
    ents = [n for n in root.children if n.name == "entity"]
    solids = []
    for w in world:
        solids += [c for c in w.children if c.name == "solid"]
    if opt.get("detail", True):
        for e in ents:
            if e.props.get("classname", "") == "func_detail":
                solids += [c for c in e.children if c.name == "solid"]
    log("Найдено брашей: %d" % len(solids))

    brushes = []
    for i, sd in enumerate(solids):
        b = build_brush(sd)
        if b:
            brushes.append(b)
        if i % 50 == 0:
            progress(0.30 * i / max(1, len(solids)))
    if not brushes:
        raise ValueError("В VMF не найдено подходящих брашей (все tools или карта пуста).")
    log("Брашей после фильтра (без tools): %d" % len(brushes))

    gmin = [min(b.bmin[a] for b in brushes) for a in range(3)]
    gmax = [max(b.bmax[a] for b in brushes) for a in range(3)]
    org = [int(math.floor(gmin[a] / unit)) for a in range(3)]
    dim = [max(1, int(math.ceil(gmax[a] / unit)) - org[a]) for a in range(3)]
    nx, ny, nz = dim
    log("Размер камеры: %d x %d x %d вокселей" % (nx, ny, nz))
    if nx * ny * nz > 4000000:
        raise ValueError("Слишком большая сетка (%d вокселей). Увеличьте размер вокселя." % (nx * ny * nz))
    if max(dim) > 30:
        log("ВНИМАНИЕ: размер больше ~30 вокселей по оси - редактор Portal 2 может не открыть такую карту.")

    def idx(x, y, z):
        return x + nx * (y + ny * z)

    masks, bmasks = {}, {}
    btouch, wtouch = set(), set()
    touched = set()   # воксели, которых браш касается (даже тонко) - преграды для заливки
    for bi, br in enumerate(brushes):
        x0 = int(math.floor(br.bmin[0] / unit)); x1 = max(x0, int(math.ceil(br.bmax[0] / unit)) - 1)
        y0 = int(math.floor(br.bmin[1] / unit)); y1 = max(y0, int(math.ceil(br.bmax[1] / unit)) - 1)
        z0 = int(math.floor(br.bmin[2] / unit)); z1 = max(z0, int(math.ceil(br.bmax[2] / unit)) - 1)
        planes = br.planes
        for ix in range(x0, x1 + 1):
            lx = ix * unit; hx = lx + unit
            for iy in range(y0, y1 + 1):
                ly = iy * unit; hy = ly + unit
                for iz in range(z0, z1 + 1):
                    lz = iz * unit; hz = lz + unit
                    key = idx(ix - org[0], iy - org[1], iz - org[2])
                    cur = masks.get(key, 0)
                    if cur == full_mask:
                        continue
                    outside = False
                    full = True
                    for nxp, nyp, nzp, d in planes:
                        mn = (nxp * (lx if nxp > 0 else hx) + nyp * (ly if nyp > 0 else hy)
                              + nzp * (lz if nzp > 0 else hz))
                        if mn > d + EPS:
                            outside = True
                            break
                        mx = (nxp * (hx if nxp > 0 else lx) + nyp * (hy if nyp > 0 else ly)
                              + nzp * (hz if nzp > 0 else lz))
                        if mx > d:
                            full = False
                    if outside:
                        continue
                    touched.add(key)
                    (btouch if br.black else wtouch).add(key)
                    if full:
                        m = full_mask
                    else:
                        m = 0
                        bit = 0
                        for a in range(s):
                            x = lx + offs[a]
                            for b in range(s):
                                y = ly + offs[b]
                                for c in range(s):
                                    z = lz + offs[c]
                                    ok = True
                                    for nxp, nyp, nzp, d in planes:
                                        if nxp * x + nyp * y + nzp * z > d + EPS:
                                            ok = False
                                            break
                                    if ok:
                                        m |= 1 << bit
                                    bit += 1
                    if m:
                        masks[key] = cur | m
                        if br.black:
                            bmasks[key] = bmasks.get(key, 0) | m
        if bi % 20 == 0:
            progress(0.30 + 0.50 * bi / len(brushes))

    total = nx * ny * nz
    solid = bytearray(total)
    black = bytearray(total)
    for key, m in masks.items():
        if popcount(m) >= need_bits:
            solid[key] = 1
            bm = bmasks.get(key, 0)
            if bm and popcount(bm) * 2 > popcount(m):
                black[key] = 1
    log("Твёрдых вокселей после порога: %d" % sum(solid))

    def to_vox(p):
        return (int(math.floor(p[0] / unit)) - org[0],
                int(math.floor(p[1] / unit)) - org[1],
                int(math.floor(p[2] / unit)) - org[2])

    def inside(v):
        return 0 <= v[0] < nx and 0 <= v[1] < ny and 0 <= v[2] < nz

    # --- точки входа / выхода ---
    spawn = None
    exit_pos = None
    for e in ents:
        cl = e.props.get("classname", "")
        if spawn is None and cl in ("info_player_start", "info_coop_spawn"):
            o = _origin(e)
            if o:
                spawn = to_vox((o[0], o[1], o[2] + 32))
    for e in ents:
        cl = e.props.get("classname", "")
        tn = e.props.get("targetname", "").lower()
        if cl == "trigger_changelevel":
            bs = [build_brush(c, skip_tools=False) for c in e.children if c.name == "solid"]
            bs = [b for b in bs if b]
            if bs:
                cx = sum((b.bmin[0] + b.bmax[0]) / 2 for b in bs) / len(bs)
                cy = sum((b.bmin[1] + b.bmax[1]) / 2 for b in bs) / len(bs)
                cz = sum((b.bmin[2] + b.bmax[2]) / 2 for b in bs) / len(bs)
                exit_pos = to_vox((cx, cy, cz))
                break
        elif "exit" in tn and _origin(e):
            exit_pos = to_vox(_origin(e))
            break

    # --- заливка снаружи ---
    if opt.get("flood", True):
        if spawn and inside(spawn):
            v = spawn
            while inside(v) and solid[idx(*v)]:
                v = (v[0], v[1], v[2] + 1)
            if inside(v):
                seen = bytearray(total)
                dq = deque([v])
                seen[idx(*v)] = 1
                leak = False
                while dq:
                    x, y, z = dq.popleft()
                    if x in (0, nx - 1) or y in (0, ny - 1) or z in (0, nz - 1):
                        leak = True
                    for dx, dy, dz in ((1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)):
                        X, Y, Z = x + dx, y + dy, z + dz
                        if 0 <= X < nx and 0 <= Y < ny and 0 <= Z < nz:
                            k = idx(X, Y, Z)
                            if not seen[k] and not solid[k] and k not in touched:
                                seen[k] = 1
                                dq.append((X, Y, Z))
                filled = 0
                for k in range(total):
                    if not seen[k] and not solid[k]:
                        solid[k] = 1
                        filled += 1
                        if k in btouch and k not in wtouch:
                            black[k] = 1
                log("Заливка: закрашено вокселей вне комнаты: %d" % filled)
                if leak:
                    log("ВНИМАНИЕ: заливка дошла до края сетки - комната, похоже, не замкнута "
                        "(или стены тоньше порога). Уменьшите порог / увеличьте число сэмплов.")
            else:
                log("Заливка пропущена: нет свободного вокселя над точкой спавна.")
        else:
            log("Заливка пропущена: info_player_start не найден (или вне сетки).")
    progress(0.85)

    # --- рамка ---
    if opt.get("border", False):
        ox_, oy_, oz_ = 1, 1, 1
        nnx, nny, nnz = nx + 2, ny + 2, nz + 2
        ns = bytearray(nnx * nny * nnz)
        nbk = bytearray(nnx * nny * nnz)
        for z in range(nnz):
            for y in range(nny):
                for x in range(nnx):
                    k2 = x + nnx * (y + nny * z)
                    if x in (0, nnx - 1) or y in (0, nny - 1) or z in (0, nnz - 1):
                        ns[k2] = 1
                    else:
                        k1 = idx(x - 1, y - 1, z - 1)
                        ns[k2] = solid[k1]
                        nbk[k2] = black[k1]
        solid, black = ns, nbk
        if spawn:
            spawn = (spawn[0] + 1, spawn[1] + 1, spawn[2] + 1)
        if exit_pos:
            exit_pos = (exit_pos[0] + 1, exit_pos[1] + 1, exit_pos[2] + 1)
        nx, ny, nz = nnx, nny, nnz

        def idx(x, y, z):  # noqa: F811
            return x + nx * (y + ny * z)

    def is_solid(x, y, z):
        if 0 <= x < nx and 0 <= y < ny and 0 <= z < nz:
            return solid[x + nx * (y + ny * z)] == 1
        return False

    def is_black(x, y, z):
        if 0 <= x < nx and 0 <= y < ny and 0 <= z < nz:
            return black[x + nx * (y + ny * z)] == 1
        return False

    pmode = opt.get("portal", "all")

    def portal_flag(x, y, z, axis):
        bx, by, bz = x, y, z
        if axis == 0:
            bx -= 1
        elif axis == 1:
            by -= 1
        else:
            bz -= 1
        a, b = is_solid(x, y, z), is_solid(bx, by, bz)
        if pmode == "none":
            return 0
        if pmode == "material":
            if a and not b:
                return 0 if is_black(x, y, z) else 1
            if b and not a:
                return 0 if is_black(bx, by, bz) else 1
        return 1

    # --- запись P2C ---
    now = int(time.time())
    title = opt.get("title") or os.path.splitext(os.path.basename(vmf_path))[0]
    desc = opt.get("desc", "Converted from VMF")
    lines = []
    A = lines.append
    A('"portal2_puzzle"')
    A("{")
    A('\t"AppID"\t\t"644"')
    A('\t"Version"\t\t"%s"' % opt.get("version", "14"))
    A('\t"FileID"\t\t"0x0000000000000000"')
    A('\t"Timestamp_Created"\t\t"0x%016X"' % now)
    A('\t"Timestamp_Modified"\t\t"0x%016X"' % now)
    A('\t"CompileTime"\t\t"15.000000"')
    A('\t"Title"\t\t"%s"' % _q(title))
    A('\t"Description"\t\t"%s"' % _q(desc))
    A('\t"PreviewDirty"\t\t"1"')
    A('\t"ChamberSize"\t\t"%d %d %d"' % (nx, ny, nz))
    A('\t"Voxels"')
    A("\t{")
    written = 0
    for z in range(nz + 1):
        for y in range(ny + 1):
            for x in range(nx + 1):
                if not (is_solid(x, y, z) or is_solid(x - 1, y, z)
                        or is_solid(x, y - 1, z) or is_solid(x, y, z - 1)):
                    continue
                A('\t\t"Voxel"')
                A("\t\t{")
                A('\t\t\t"Position"\t\t"%d %d %d"' % (x, y, z))
                A('\t\t\t"Solid"\t\t"%d"' % (1 if is_solid(x, y, z) else 0))
                A('\t\t\t"Portal0"\t\t"%d"' % portal_flag(x, y, z, 0))
                A('\t\t\t"Portal1"\t\t"%d"' % portal_flag(x, y, z, 1))
                A('\t\t\t"Portal2"\t\t"%d"' % portal_flag(x, y, z, 2))
                A("\t\t}")
                written += 1
    A("\t}")

    A('\t"Items"')
    A("\t{")
    index = 0
    items_info = []
    if opt.get("doors", True):
        door_list = []
        if spawn:
            door_list.append(("ITEM_ENTRY_DOOR", spawn, opt.get("entry_angles", "-90 -90 0")))
        else:
            log("Вход: info_player_start не найден, дверь входа не добавлена.")
        if exit_pos:
            door_list.append(("ITEM_EXIT_DOOR", exit_pos, opt.get("exit_angles", "-90 0 0")))
        else:
            log("Выход: не найден trigger_changelevel / entity с 'exit' в targetname, "
                "дверь выхода не добавлена.")
        for typ, pos, ang in door_list:
            A('\t\t"Item"')
            A("\t\t{")
            A('\t\t\t"Index"\t\t"%d"' % index)
            A('\t\t\t"Type"\t\t"%s"' % typ)
            A('\t\t\t"Deletable"\t\t"0"')
            A('\t\t\t"VoxelPos"\t\t"%d %d %d"' % pos)
            A('\t\t\t"LocalPos"\t\t"0 0 0"')
            A('\t\t\t"Angles"\t\t"%s"' % ang)
            A('\t\t\t"Facing"\t\t"0 0 0"')
            A("\t\t}")
            items_info.append((typ, pos))
            index += 1
    A("\t}")
    A('\t"Connections"')
    A("\t{")
    A("\t}")
    A("}")

    with open(out_path, "w", encoding="utf-8", newline="\n") as f:
        f.write("\n".join(lines) + "\n")
    progress(1.0)
    log("Готово: %s (воксельных записей: %d, предметов: %d)" % (out_path, written, index))
    return {"nx": nx, "ny": ny, "nz": nz, "solid": bytes(solid),
            "spawn": spawn, "exit": exit_pos}


# --------------------------------------------------------------------------
#  Интерфейс
# --------------------------------------------------------------------------
def run_gui():
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox

    root = tk.Tk()
    root.title("VMF → P2C (Portal 2 Puzzle Maker)")
    root.geometry("980x700")

    v_in = tk.StringVar()
    v_out = tk.StringVar()
    v_title = tk.StringVar()
    v_desc = tk.StringVar(value="Converted from VMF")
    v_unit = tk.StringVar(value="128")
    v_samples = tk.StringVar(value="4")
    v_thr = tk.StringVar(value="25")
    v_detail = tk.BooleanVar(value=True)
    v_flood = tk.BooleanVar(value=True)
    v_border = tk.BooleanVar(value=False)
    v_doors = tk.BooleanVar(value=True)
    v_portal = tk.StringVar(value="material")
    v_entry_ang = tk.StringVar(value="-90 -90 0")
    v_exit_ang = tk.StringVar(value="-90 0 0")

    state = {"res": None, "q": None}

    left = ttk.Frame(root, padding=8)
    left.pack(side="left", fill="y")
    right = ttk.Frame(root, padding=8)
    right.pack(side="right", fill="both", expand=True)

    def row(parent, r, label, widget):
        ttk.Label(parent, text=label).grid(row=r, column=0, sticky="w", pady=2)
        widget.grid(row=r, column=1, sticky="we", pady=2, padx=4)

    def browse_in():
        p = filedialog.askopenfilename(title="Выберите VMF", filetypes=[("Valve Map", "*.vmf"), ("Все", "*.*")])
        if p:
            v_in.set(p)
            if not v_out.get():
                v_out.set(os.path.splitext(p)[0] + ".p2c")
            if not v_title.get():
                v_title.set(os.path.splitext(os.path.basename(p))[0])

    def browse_out():
        p = filedialog.asksaveasfilename(title="Сохранить P2C", defaultextension=".p2c",
                                         filetypes=[("Portal 2 puzzle", "*.p2c")])
        if p:
            v_out.set(p)

    f1 = ttk.Frame(left)
    ttk.Entry(f1, textvariable=v_in, width=34).pack(side="left", fill="x", expand=True)
    ttk.Button(f1, text="...", width=3, command=browse_in).pack(side="left", padx=2)
    row(left, 0, "Файл VMF:", f1)
    f2 = ttk.Frame(left)
    ttk.Entry(f2, textvariable=v_out, width=34).pack(side="left", fill="x", expand=True)
    ttk.Button(f2, text="...", width=3, command=browse_out).pack(side="left", padx=2)
    row(left, 1, "Файл P2C:", f2)
    row(left, 2, "Название:", ttk.Entry(left, textvariable=v_title))
    row(left, 3, "Описание:", ttk.Entry(left, textvariable=v_desc))

    ttk.Separator(left).grid(row=4, column=0, columnspan=2, sticky="we", pady=6)
    row(left, 5, "Юнитов на воксель:", ttk.Spinbox(left, from_=16, to=1024, increment=16, textvariable=v_unit, width=8))
    row(left, 6, "Сэмплов на ось (1-8):", ttk.Spinbox(left, from_=1, to=8, textvariable=v_samples, width=8))
    row(left, 7, "Порог заполнения, %:", ttk.Spinbox(left, from_=1, to=100, textvariable=v_thr, width=8))
    cb = ttk.Combobox(left, state="readonly", textvariable=v_portal,
                      values=["all", "none", "material"], width=10)
    row(left, 8, "Порталы на стенах:", cb)
    ttk.Label(left, text="all = везде, none = нигде,\nmaterial = чёрные материалы без порталов",
              foreground="#666").grid(row=9, column=0, columnspan=2, sticky="w")

    ttk.Checkbutton(left, text="Включать func_detail", variable=v_detail).grid(row=10, column=0, columnspan=2, sticky="w")
    ttk.Checkbutton(left, text="Залить всё вне комнаты (от info_player_start)", variable=v_flood).grid(row=11, column=0, columnspan=2, sticky="w")
    ttk.Checkbutton(left, text="Добавить внешнюю рамку из твёрдых вокселей", variable=v_border).grid(row=12, column=0, columnspan=2, sticky="w")
    ttk.Checkbutton(left, text="Добавить двери входа/выхода", variable=v_doors).grid(row=13, column=0, columnspan=2, sticky="w")
    row(left, 14, "Angles входа:", ttk.Entry(left, textvariable=v_entry_ang, width=12))
    row(left, 15, "Angles выхода:", ttk.Entry(left, textvariable=v_exit_ang, width=12))

    btn = ttk.Button(left, text="Конвертировать")
    btn.grid(row=16, column=0, columnspan=2, sticky="we", pady=10)
    pb = ttk.Progressbar(left, maximum=1.0)
    pb.grid(row=17, column=0, columnspan=2, sticky="we")
    left.columnconfigure(1, weight=1)

    # правая часть: лог + просмотр слоя
    logbox = tk.Text(right, height=10, state="disabled", wrap="word")
    logbox.pack(fill="x")
    ttk.Label(right, text="Предпросмотр слоя (серый = твёрдый, зелёный = вход, красный = выход):").pack(anchor="w", pady=(8, 0))
    canvas = tk.Canvas(right, bg="white", highlightthickness=1, highlightbackground="#999")
    canvas.pack(fill="both", expand=True)
    layer = tk.Scale(right, from_=0, to=0, orient="horizontal", label="Слой Z")
    layer.pack(fill="x")

    def log(msg):
        logbox.configure(state="normal")
        logbox.insert("end", msg + "\n")
        logbox.see("end")
        logbox.configure(state="disabled")

    def draw(*_):
        r = state["res"]
        canvas.delete("all")
        if not r:
            return
        nx, ny = r["nx"], r["ny"]
        z = int(layer.get())
        cs = max(2, min(24, 460 // max(nx, ny)))
        sol = r["solid"]
        for y in range(ny):
            for x in range(nx):
                k = x + nx * (y + ny * z)
                col = "#555555" if sol[k] else "#eeeeee"
                X0, Y0 = x * cs + 4, (ny - 1 - y) * cs + 4
                canvas.create_rectangle(X0, Y0, X0 + cs, Y0 + cs, fill=col, outline="#cccccc")
        for key, color in (("spawn", "#22aa22"), ("exit", "#dd2222")):
            p = r[key]
            if p and p[2] == z:
                X0, Y0 = p[0] * cs + 4, (ny - 1 - p[1]) * cs + 4
                canvas.create_rectangle(X0, Y0, X0 + cs, Y0 + cs, fill=color, outline="black")

    layer.configure(command=draw)

    def poll():
        q = state["q"]
        try:
            while True:
                item = q.get_nowait()
                if item[0] == "log":
                    log(item[1])
                elif item[0] == "prog":
                    pb["value"] = item[1]
                elif item[0] == "done":
                    state["res"] = item[1]
                    layer.configure(to=max(0, item[1]["nz"] - 1))
                    layer.set(0)
                    draw()
                    btn.configure(state="normal")
                    messagebox.showinfo("Готово", "Файл сохранён:\n" + v_out.get())
                    return
                elif item[0] == "err":
                    log("ОШИБКА: " + item[1])
                    log(item[2])
                    btn.configure(state="normal")
                    messagebox.showerror("Ошибка", item[1])
                    return
        except queue.Empty:
            pass
        root.after(100, poll)

    def start():
        if not v_in.get() or not os.path.isfile(v_in.get()):
            messagebox.showwarning("Нет файла", "Выберите существующий VMF-файл.")
            return
        if not v_out.get():
            messagebox.showwarning("Нет файла", "Укажите, куда сохранить P2C.")
            return
        try:
            opt = {
                "unit": float(v_unit.get()),
                "samples": max(1, min(8, int(v_samples.get()))),
                "threshold": float(v_thr.get()),
                "detail": v_detail.get(),
                "flood": v_flood.get(),
                "border": v_border.get(),
                "doors": v_doors.get(),
                "portal": v_portal.get(),
                "title": v_title.get(),
                "desc": v_desc.get(),
                "entry_angles": v_entry_ang.get(),
                "exit_angles": v_exit_ang.get(),
            }
        except ValueError:
            messagebox.showwarning("Неверные значения", "Проверьте числовые поля.")
            return
        btn.configure(state="disabled")
        pb["value"] = 0
        q = queue.Queue()
        state["q"] = q

        def work():
            try:
                res = convert(v_in.get(), v_out.get(), opt,
                              log=lambda m: q.put(("log", m)),
                              progress=lambda f: q.put(("prog", f)))
                q.put(("done", res))
            except Exception as e:  # noqa: BLE001
                import traceback
                q.put(("err", str(e), traceback.format_exc()))

        threading.Thread(target=work, daemon=True).start()
        root.after(100, poll)

    btn.configure(command=start)
    root.mainloop()


if __name__ == "__main__":
    if len(sys.argv) >= 3:
        o = {}
        if len(sys.argv) >= 4:
            o["unit"] = float(sys.argv[3])
        convert(sys.argv[1], sys.argv[2], o)
    else:
        run_gui()
