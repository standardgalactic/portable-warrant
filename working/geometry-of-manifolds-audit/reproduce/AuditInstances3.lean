import Atlas.GeometryOfManifolds.GeometryOfManifolds
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let classes : List Name := [`IsCompactOrientedRiemannian, `HasSobolevSpaces, `IsCompactSymplectic, `IsEllipticEndo, `HasGreenOperatorDecomp, `HasRelativeHomotopyOperator, `HasTubularExpMapData, `HasIFTData, `HamiltonianFlow, `IsKahler, `HasParametrixDFS]
  let found := env.constants.fold (init := (#[] : Array (Name × Name))) fun acc n ci =>
    match ci with
    | .defnInfo _ | .thmInfo _ =>
      let b := ci.type.getForallBody
      match b.getAppFn.constName? with
      | some hd =>
        let hd' := if hd == `Nonempty then (b.appArg!.getForallBody.getAppFn.constName?).getD hd else hd
        if classes.contains hd' && (n.getRoot != `Mathlib) then acc.push (hd', n) else acc
      | none => acc
    | _ => acc
  for cls in classes do
    let xs := (found.filter (·.1 == cls)).map (·.2)
    logInfo m!"{cls}: {xs.size}: {xs}"
