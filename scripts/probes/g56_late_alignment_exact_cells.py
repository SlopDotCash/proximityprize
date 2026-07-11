#!/usr/bin/env python3
import importlib.util
import os
spec=importlib.util.spec_from_file_location('probe',os.path.join(os.path.dirname(os.path.abspath(__file__)),'g56_late_alignment_probe.py'))
probe=importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)
for n,p in [(16,97),(16,193),(32,257),(32,449),(32,769),(64,1217)]:
    for r in (5,6):
        d=probe.row(n,p,r)
        print(n,p,r,'A=',d['A'],'C12=',d['C12'],'baseline=',n*n*d['totalR'],'ratio=',d['ratio'],'rho=',d['rho'])
