# ToN Toolkit

A desktop helper for **Terrors of Nowhere** in VRChat. It reads the VRChat log
and OSC speed data to spot round types before the round starts, and can handle
the repetitive parts of a lobby.

Windows only. Desktop mode.

## What it does

**8 Page / Punished Detector** — measures your movement speed in the lobby to
identify 8ページ (a 6.50 m/s sideways cap) and パニッシュ (a slow cap) before
the round begins. Press your check key when you hear the start button, or let
it check automatically. Alerts play a sound you choose.

**Auto Explode** — holds your self-destruct key when a round you ticked starts.
Stands down if you are moving, and a cancel key stops it instantly.

**Auto Round Starter** — walks to the start button and presses it after a round
ends. Friends+ or private instances only.

## Requirements

- VRChat with **OSC enabled** (radial menu → Options → OSC → Enable)
- Windows

## Running from the exe

Download the zip from Releases, extract it anywhere, run `ToNToolkit.exe`.
Settings are saved beside it as `ton_toolkit.json`.

## Running from source

```
pip install python-osc zeroconf
python ton_toolkit.py
```

## Building

Put `ton_toolkit.py`, `icon.ico` and `Sounds\` in one folder and run:

```
build_release.bat
```

You get `dist\ToNToolkit\` to run and `release\ToNToolkit-vX.X.zip` to attach
to a GitHub release.

## Alert sounds

Drop `.wav` files in `Sounds\` and pick them on the detector tab. A `Sounds`
folder next to the exe overrides the bundled copies, so they can be changed
without rebuilding.

## Notes and limits

- **One VRChat at a time.** The toolkit controls a single client. With more
  than one VRChat open, the self-destruct key goes to whichever window has
  focus, which may not be the one you meant.
- **Background explode** works while you are in another window, but only with
  one VRChat running — see the warning on that setting.
- The round starter needs the cursor over the button, because VRChat aims
  interactions from the mouse rather than the camera. It moves the pointer for
  the click and puts it back.
- If port 9001 is taken by another OSC app, the toolkit falls back to OSCQuery
  so both can run.

## Licence

MIT — see [LICENSE](LICENSE). You may use, modify and redistribute it,
including in your own projects, as long as the copyright notice stays with it.
It comes with no warranty.

## Disclaimer

Unofficial fan tool, not affiliated with VRChat Inc. or the creators of
Terrors of Nowhere. Automation carries risk and may be unwelcome in some
instances — please read [DISCLAIMER.md](DISCLAIMER.md) before using it.
