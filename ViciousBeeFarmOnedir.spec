# -*- mode: python ; coding: utf-8 -*-


a = Analysis(
    ['launcher.py'],
    pathex=[],
    binaries=[],
    datas=[],
    hiddenimports=[],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    # The runtime uses OpenCV + ONNX Runtime only. Training is performed
    # separately, so do not embed PyTorch/CUDA and its training ecosystem.
    excludes=[
        'torch',
        'torchvision',
        'torchaudio',
        'ultralytics',
        'triton',
        'functorch',
        'torchgen',
        'matplotlib',
        'scipy',
        'sympy',
        'pandas',
        'seaborn',
    ],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    [],
    exclude_binaries=True,
    name='ViciousBeeFarm',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
)

coll = COLLECT(
    exe,
    a.binaries,
    a.datas,
    strip=False,
    upx=True,
    upx_exclude=[],
    name='ViciousBeeFarm_onedir',
)
