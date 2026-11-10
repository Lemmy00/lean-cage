import LeanCageHost.GatewayWire

namespace LeanCage.Host.Cli

def usage : ByteArray := ("usage: leancage [--bundle PATH] [--results PATH] " ++
  "{check,run,validate-policy,report,bundle} ...\n" ++
  "run/check POLICY [--workspace PATH] [--stdin PATH] [--output PATH] [--timeout SECONDS]\n").toUTF8

structure Parsed where
  request : GatewayWire.Request
  timeoutNanoseconds : Option Nat := none

inductive Action where
  | help
  | command (parsed : Parsed)

def decodeArguments (bytes : ByteArray) : Except String (List ByteArray) := do
  if bytes.size > reportMax then throw "CLI arguments exceed 65536 bytes"
  if bytes.isEmpty then return []
  if bytes[bytes.size - 1]! != 0 then throw "unterminated CLI argument list"
  return (bytes.data.toList.splitOn 0).dropLast.map (fun value => ByteArray.mk value.toArray)

def pathField (bytes : ByteArray) : Except String GatewayWire.Field := do
  let field := GatewayWire.Field.mk GatewayWire.pathKind
    (if bytes.isEmpty then ".".toUTF8 else bytes)
  if !GatewayWire.pathValid field then throw "CLI path exceeds its supported bound"
  return field

def splitOption (bytes : ByteArray) : ByteArray × Option ByteArray :=
  let parts := bytes.data.toList.splitOn 61
  match parts with
  | [] => (bytes, none)
  | [_] => (bytes, none)
  | first :: rest =>
    (ByteArray.mk first.toArray, some (ByteArray.mk (List.intercalate [61] rest).toArray))

def optionValue (inlineValue : Option ByteArray) (rest : List ByteArray) :
    Except String (ByteArray × List ByteArray) :=
  match inlineValue, rest with
  | some value, _ => .ok (value, rest)
  | none, value :: rest => .ok (value, rest)
  | _, _ => .error "CLI option requires a value"

-- §FS-host-boundary.caller: Decimal CLI timeouts denote a positive bounded rational duration.
def timeout (bytes : ByteArray) : Except String Nat := do
  if bytes.size > 128 then throw "CLI timeout exceeds its supported numeric bound"
  let some text := String.fromUTF8? bytes | throw "invalid CLI timeout encoding"
  let text := if text.startsWith "+" then (text.drop 1).toString else text
  let pieces := (text.replace "E" "e").splitOn "e"
  if pieces.length > 2 then throw "invalid CLI timeout exponent"
  let mantissa := pieces.head!
  if mantissa.startsWith "-" then throw "VM timeout must be positive"
  let decimal := mantissa.splitOn "."
  if decimal.length > 2 then throw "invalid CLI timeout fraction"
  let digits := String.join decimal
  if digits.isEmpty || !digits.toList.all (fun c => '0' ≤ c && c ≤ '9') then
    throw "invalid CLI timeout digits"
  let some significand := digits.toNat? | throw "invalid CLI timeout significand"
  if significand == 0 then throw "VM timeout must be positive"
  let exponentText := (pieces[1]?).getD "0"
  let some exponent := exponentText.toInt? | throw "invalid CLI timeout exponent"
  if exponent.natAbs > 400 then throw "CLI timeout exponent is outside its supported bound"
  let fraction := (decimal[1]?).map String.length |>.getD 0
  let power := exponent - Int.ofNat fraction
  if power > 4 then throw "VM timeout is outside the supported bound"
  let numerator := if power ≥ 0 then significand * 10 ^ power.toNat else significand
  let denominator := if power < 0 then 10 ^ power.natAbs else 1
  if numerator > 3660 * denominator then throw "VM timeout is outside the supported bound"
  return (numerator * 1000000000 + denominator - 1) / denominator

def commandCode (name : ByteArray) : Option Nat :=
  if name == "validate-policy".toUTF8 then some GatewayWire.validateCommand
  else if name == "check".toUTF8 then some GatewayWire.checkCommand
  else if name == "run".toUTF8 then some GatewayWire.runCommand
  else if name == "report".toUTF8 then some GatewayWire.reportCommand
  else if name == "bundle".toUTF8 then some GatewayWire.bundleCommand
  else none

def finish (command : Nat) (fields : Array GatewayWire.Field) (positionals : List ByteArray)
    (duration : Option Nat) : Except String Parsed := do
  let fields ← if command == GatewayWire.bundleCommand then do
      if !positionals.isEmpty then throw "bundle does not accept a positional argument"
      pure fields
    else do
      let [argument] := positionals | throw "command requires exactly one policy or request"
      let field ← pathField argument
      pure (fields.set! (if command == GatewayWire.reportCommand then
        GatewayWire.lookupSlot else GatewayWire.policySlot) field)
  let request := GatewayWire.Request.mk command 0 fields
  if !request.valid then throw "invalid CLI command option combination"
  return ⟨request, duration⟩

-- §FS-host-boundary.caller: Consume arguments once; select only fixed command names.
def parseLoop : Nat → List ByteArray → Option Nat → Array GatewayWire.Field →
    List ByteArray → Option Nat → Except String Action
  | 0, _, _, _, _, _ => .error "CLI argument parser made no bounded progress"
  | fuel + 1, arguments, command, fields, positionals, duration => do
    match arguments with
    | [] =>
      let some command := command | throw "a CLI command is required"
      return .command (← finish command fields positionals.reverse duration)
    | argument :: rest =>
      if argument == "--".toUTF8 then
        let some command := command | throw "a CLI command is required before --"
        return .command (← finish command fields (positionals.reverse ++ rest) duration)
      if argument == "--help".toUTF8 || argument == "-h".toUTF8 then return .help
      let (option, inlineValue) := splitOption argument
      let global := option == "--bundle".toUTF8 || option == "--results".toUTF8
      let localOption := option == "--workspace".toUTF8 || option == "--stdin".toUTF8 ||
        option == "--output".toUTF8 || option == "--timeout".toUTF8
      if global || localOption then
        if global && command.isSome then throw "global CLI options precede the command"
        if localOption && !(command == some GatewayWire.runCommand || command == some GatewayWire.checkCommand) then
          throw "workload CLI option requires run or check"
        let (value, rest) ← optionValue inlineValue rest
        if option == "--timeout".toUTF8 then
          parseLoop fuel rest command fields positionals (some (← timeout value))
        else
          let slot := if option == "--bundle".toUTF8 then GatewayWire.bundleSlot
            else if option == "--results".toUTF8 then GatewayWire.resultsSlot
            else if option == "--workspace".toUTF8 then GatewayWire.workspaceSlot
            else if option == "--stdin".toUTF8 then GatewayWire.stdinSlot else GatewayWire.outputSlot
          let field ← pathField value
          parseLoop fuel rest command (fields.set! slot field) positionals duration
      else if argument.data[0]? == some 45 then throw "unknown CLI option"
      else match command with
        | none =>
          let some command := commandCode argument | throw "unknown CLI command"
          parseLoop fuel rest (some command) fields positionals duration
        | some command =>
          if !positionals.isEmpty then throw "too many CLI positional arguments"
          parseLoop fuel rest (some command) fields (argument :: positionals) duration

def parse (request : GatewayWire.Request) : Except String Action := do
  let arguments ← decodeArguments (request.field GatewayWire.policySlot).bytes
  let fields := (Array.replicate 8 ({} : GatewayWire.Field)).set! GatewayWire.bundleSlot
    (request.field GatewayWire.bundleSlot)
  let fields := fields.set! GatewayWire.resultsSlot (request.field GatewayWire.resultsSlot)
  parseLoop (arguments.length + 1) arguments none fields [] none

end LeanCage.Host.Cli
