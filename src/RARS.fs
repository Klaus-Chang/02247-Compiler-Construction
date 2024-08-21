// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Utility functions to launch RARS (RISC-V Assembler and Runtime Simulator)
/// from the hyggec compiler.
module RARS

/// Error code to signal a RARS assembly error
let asmErrCode: int = 15


// Error code to signal a RARS simulation error
let simErrCode: int = 16


/// Explain the meaning of RARS exit codes.
let explainExitCode (exit: int): string =
    match exit with
    | n when n = RISCVCodegen.assertExitCode ->
        "assertion violation in source program"
    | n when n = asmErrCode ->
        "error in assembly code, likely due to a hyggec codegen bug"
    | n when n = simErrCode ->
        "simulation error, maybe due to a hyggec codegen bug"
    | 0 -> "successful termination"
    | _ -> "other failure while launching or running RARS"


/// Launch RARS on the given assembly code.  If 'warnOnAssertFailure' is true,
/// then log a warning if the RARS exit code denotes an assertion failure.
/// Return the RARS exit code: 0 on success, non-zero in case of error.
let launch (asm: string) (warnOnAssertFailure: bool): int =
    let curDir = System.IO.Directory.GetCurrentDirectory()
    let rars = System.IO.Path.Combine [| curDir; "lib"; "rars.jar" |]
    try
        let tmpDir = Util.mkTempDir "hyggec-"
        Log.debug $"Created temporary directory: %s{tmpDir}"
        let asmFile = System.IO.Path.Combine [| tmpDir; "code.asm" |]
        try
            System.IO.File.WriteAllText(asmFile, asm)
            Log.debug $"Saved assembly code in: %s{asmFile}"
            use p = new System.Diagnostics.Process();
            p.StartInfo.FileName <- "java";
            // For the meaning of RARS command line arguments, see:
            // https://github.com/TheThirdOne/rars/wiki/Using-the-command-line
            let rarsArgs = ["-jar"; $"%s{rars}";
                            $"ae%d{asmErrCode}";
                            $"se%d{simErrCode}";
                            "me"; "nc"; "sm"; "ic";
                            $"%s{asmFile}"]
            for arg in rarsArgs do
                p.StartInfo.ArgumentList.Add(arg)

            p.StartInfo.RedirectStandardOutput <- false
            p.StartInfo.RedirectStandardError <- true
            p.StartInfo.RedirectStandardInput <- false
            p.StartInfo.UseShellExecute <- false
            try
                let formatArgs x y = $"%s{x} %s{y}"
                Log.info $"Launching RARS: %s{p.StartInfo.FileName} %O{Seq.reduce formatArgs p.StartInfo.ArgumentList}"
                p.Start() |> ignore
                p.WaitForExit()
                let stdErr = p.StandardError.ReadToEnd()
                let explain = explainExitCode p.ExitCode
                if (p.ExitCode = asmErrCode) || (p.ExitCode = simErrCode) then
                    Log.error ($"BUG: RARS exited with code %d{p.ExitCode} (%s{explain}) "
                               + $"while loading or running %s{asmFile}")
                    Log.error $"- - - - - - - - - - RARS output starts here - - - - - - - - - -%s{Util.nl}%s{stdErr}"
                    Log.error $"- - - - - - - - - - RARS output ends here - - - - - - - - - - -"
                    // Log.error $"Assembly code produced by hyggec:%s{Util.nl}%s{asm}"
                    p.ExitCode
                else if (p.ExitCode = 0) || (p.ExitCode = RISCVCodegen.assertExitCode) then
                    if p.ExitCode = RISCVCodegen.assertExitCode && warnOnAssertFailure then
                        Log.warning $"RARS exited with code: %d{p.ExitCode} (%s{explain})"
                    else
                        Log.info $"RARS exited with code: %d{p.ExitCode} (%s{explain})"
                    Log.debug $"RARS output:%s{Util.nl}%s{stdErr}"
                    try
                        Log.debug $"Removing temporary directory: %s{tmpDir}"
                        System.IO.Directory.Delete(tmpDir, true)
                        p.ExitCode
                    with e ->
                        Log.error $"Error deleting temporary directory %s{tmpDir}: %s{e.Message}"
                        1 // Non-zero exit code
                else
                    Log.error $"BUG: unexpected RARS exit code %d{p.ExitCode}"
                    p.ExitCode // Non-zero exit code
            with e ->
                Log.error $"Error launching RARS: %s{e.Message}"
                1 // Non-zero exit code
        with e ->
            Log.error $"Error writing file %s{asmFile}: %s{e.Message}"
            1 // Non-zero exit code
    with e ->
        Log.error $"Error creating temporary directory: %s{e.Message}"
        1 // Non-zero exit code
