import Atlas.GeometryOfManifolds.GeometryOfManifolds
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let st := Meta.instanceExtension.getState env
  for cls in [`IsCompactOrientedRiemannian, `IsCompactManifold, `HasSobolevSpaces, `IsCompactSymplectic, `HasLieBracket, `IsEuclideanDFS, `DifferentialFormSpace] do
    let mut found : Array Name := #[]
    for (n, _) in st.instanceNames.toList do
      if let some ci := env.find? n then
        if ci.type.getForallBody.getAppFn.constName? == some cls then
          found := found.push n
    logInfo m!"{cls}: {found}"
