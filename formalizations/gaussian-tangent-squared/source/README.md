# Gaussian integrals with squared shifted tangent poles

See Prompt.txt for the full mathematical task, Walkthrough.txt for the ordered proof explanation, and TangentSquared/Final.lean for the complete theorem. The required declaration is TangentSquaredTask.gaussian_tangent_squared_poles. TuringTask, ShiftedCosine, and SimpleTangent are bundled support libraries. Rubric.csv has exactly eight criteria of weight +1.

Use the supplied offline Mathlib bundle at the pinned revision 9944fe2973b8dc0b86949101ed98232c07cd54a0 and Lean v4.33.0-rc1. Mathlib is an external dependency, not embedded in this archive.

Configure an installed bundle without downloading dependencies:

```
python3 configure_mathlib.py --mathlib /opt/mathlib4
lake --wfail build TangentSquared
lake env lean -DwarningAsError=true TangentSquared/Final.lean
lake env lean -DwarningAsError=true Audit.lean
```

For local verification, replace /opt/mathlib4 with the absolute path of the installed pinned bundle. The helper updates the Mathlib path in the lakefile and manifest, checks the toolchain and Git revision when available, and links the bundle's existing dependency cache. No compiled project output is included in the ZIP.

The strict build in the extracted project and its checks are recorded in clean-build.log, clean-final.log and clean-audit.log. Verification.json records the commands and audit results. source-hashes.sha256 records the shipped files before environment-specific configuration.
