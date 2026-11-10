import ArtifactsProofs.Blobs
import ArtifactsProofs.Manifest
import Std.Data.TreeSet.Lemmas

namespace LeanCage.Host.Artifacts

open Filesystem

def FileFromNode (blobs : BlobState) (node : Node) (file : ValidatedFile) : Prop :=
  ∃ path executable size digest blob,
    node = .file path executable size digest ∧ blobs.index[digest]? = some blob ∧
    blob.key = digest ∧ file.path = path ∧ file.executable = executable ∧
    file.bytes = blob.bytes ∧ file.digest = blob.digest ∧ file.bytes.size = size

def fileBytes (files : List ValidatedFile) : Nat := (files.map (fun file => file.bytes.size)).sum

theorem bindFiles_retains (blobs : BlobState) (nodes : List Node) (before after : BoundFiles)
    (accepted : bindFiles blobs nodes before = .ok after) :
    ∀ file ∈ before.reversed, file ∈ after.reversed := by
  induction nodes generalizing before after with
  | nil => cases accepted; exact fun _ member => member
  | cons node rest ih =>
    cases node with
    | directory path => exact ih before after accepted
    | omitted path => exact ih before after accepted
    | file path executable size digest =>
      unfold bindFiles at accepted
      dsimp only at accepted
      cases lookup : blobs.index[digest]? with
      | none => simp [lookup] at accepted
      | some blob =>
        simp only [lookup] at accepted
        split at accepted
        · contradiction
        · intro file member
          exact ih _ after accepted file (List.mem_cons_of_mem _ member)

-- §FS-host-boundary.artifacts: Each output file selects one actual manifest node and checked blob.
theorem bindFiles_provenance (blobs : BlobState) (nodes : List Node) (before after : BoundFiles)
    (accepted : bindFiles blobs nodes before = .ok after) :
    ∀ file ∈ after.reversed, file ∈ before.reversed ∨ ∃ node ∈ nodes, FileFromNode blobs node file := by
  induction nodes generalizing before after with
  | nil => cases accepted; exact fun _ member => Or.inl member
  | cons node rest ih =>
    cases node with
    | directory path =>
      intro file member
      rcases ih before after accepted file member with old | fresh
      · exact Or.inl old
      · rcases fresh with ⟨node, present, origin⟩
        exact Or.inr ⟨node, List.mem_cons_of_mem _ present, origin⟩
    | omitted path =>
      intro file member
      rcases ih before after accepted file member with old | fresh
      · exact Or.inl old
      · rcases fresh with ⟨node, present, origin⟩
        exact Or.inr ⟨node, List.mem_cons_of_mem _ present, origin⟩
    | file path executable size digest =>
      unfold bindFiles at accepted
      dsimp only at accepted
      cases lookup : blobs.index[digest]? with
      | none => simp [lookup] at accepted
      | some blob =>
        simp only [lookup] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          have fields : blob.key = digest ∧ blob.bytes.size = size := by simpa using valid
          intro file member
          rcases ih _ after accepted file member with old | fresh
          · simp only [List.mem_cons] at old
            rcases old with same | old
            · subst file
              exact Or.inr ⟨.file path executable size digest, by simp, path, executable, size, digest,
                blob, rfl, lookup, fields.1, rfl, rfl, rfl, rfl, fields.2⟩
            · exact Or.inl old
          · rcases fresh with ⟨node, present, origin⟩
            exact Or.inr ⟨node, List.mem_cons_of_mem _ present, origin⟩

theorem bindFiles_bytes (blobs : BlobState) (nodes : List Node) (before after : BoundFiles)
    (accepted : bindFiles blobs nodes before = .ok after) :
    fileBytes after.reversed = nodeBytes nodes + fileBytes before.reversed := by
  induction nodes generalizing before after with
  | nil => cases accepted; simp [nodeBytes]
  | cons node rest ih =>
    cases node with
    | directory path => simpa [nodeBytes, Node.size] using ih before after accepted
    | omitted path => simpa [nodeBytes, Node.size] using ih before after accepted
    | file path executable size digest =>
      unfold bindFiles at accepted
      dsimp only at accepted
      cases lookup : blobs.index[digest]? with
      | none => simp [lookup] at accepted
      | some blob =>
        simp only [lookup] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          have fields : blob.key = digest ∧ blob.bytes.size = size := by simpa using valid
          have total := ih _ after accepted
          change fileBytes after.reversed = nodeBytes rest +
            (blob.bytes.size + fileBytes before.reversed) at total
          simp only [nodeBytes, List.map_cons, List.sum_cons, Node.size]
          change fileBytes after.reversed = size + nodeBytes rest + fileBytes before.reversed
          rw [fields.2] at total
          omega

theorem bindFiles_count (blobs : BlobState) (nodes : List Node) (before after : BoundFiles)
    (accepted : bindFiles blobs nodes before = .ok after) :
    after.reversed.length ≤ nodes.length + before.reversed.length := by
  induction nodes generalizing before after with
  | nil => cases accepted; simp
  | cons node rest ih =>
    cases node with
    | directory path => have bound := ih before after accepted; simp only [List.length_cons]; omega
    | omitted path => have bound := ih before after accepted; simp only [List.length_cons]; omega
    | file path executable size digest =>
      unfold bindFiles at accepted
      dsimp only at accepted
      cases lookup : blobs.index[digest]? with
      | none => simp [lookup] at accepted
      | some blob =>
        simp only [lookup] at accepted
        split at accepted
        · contradiction
        · have bound := ih _ after accepted
          change after.reversed.length ≤ rest.length + (before.reversed.length + 1) at bound
          simp only [List.length_cons]
          omega

theorem bindFiles_required (blobs : BlobState) (nodes : List Node) (before after : BoundFiles)
    (accepted : bindFiles blobs nodes before = .ok after) (key : String) (member : key ∈ after.required) :
    key ∈ before.required ∨ ∃ path executable size, .file path executable size key ∈ nodes := by
  induction nodes generalizing before after with
  | nil => cases accepted; exact Or.inl member
  | cons node rest ih =>
    cases node with
    | directory path =>
      rcases ih before after accepted member with old | fresh
      · exact Or.inl old
      · rcases fresh with ⟨path, executable, size, present⟩
        exact Or.inr ⟨path, executable, size, List.mem_cons_of_mem _ present⟩
    | omitted path =>
      rcases ih before after accepted member with old | fresh
      · exact Or.inl old
      · rcases fresh with ⟨path, executable, size, present⟩
        exact Or.inr ⟨path, executable, size, List.mem_cons_of_mem _ present⟩
    | file path executable size digest =>
      unfold bindFiles at accepted
      dsimp only at accepted
      cases lookup : blobs.index[digest]? with
      | none => simp [lookup] at accepted
      | some blob =>
        simp only [lookup] at accepted
        split at accepted
        · contradiction
        · rcases ih _ after accepted member with old | fresh
          · change key ∈ before.required.insert digest at old
            rcases Std.TreeSet.mem_insert.mp old with new | previous
            · have same : digest = key := by simpa using new
              subst key
              exact Or.inr ⟨path, executable, size, by simp⟩
            · exact Or.inl previous
          · rcases fresh with ⟨path, executable, size, present⟩
            exact Or.inr ⟨path, executable, size, List.mem_cons_of_mem _ present⟩

-- §FS-host-boundary.artifacts: Every declared file has a corresponding complete output value.
theorem bindFiles_complete (blobs : BlobState) (nodes : List Node) (before after : BoundFiles)
    (accepted : bindFiles blobs nodes before = .ok after) (path : ExportPath) (executable : Bool)
    (size : Nat) (digest : String) (member : .file path executable size digest ∈ nodes) :
    ∃ file ∈ after.reversed, FileFromNode blobs (.file path executable size digest) file := by
  induction nodes generalizing before after with
  | nil => simp at member
  | cons node rest ih =>
    cases node with
    | directory name => exact ih before after accepted (by simpa using member)
    | omitted name => exact ih before after accepted (by simpa using member)
    | file name flag count key =>
      unfold bindFiles at accepted
      dsimp only at accepted
      cases lookup : blobs.index[key]? with
      | none => simp [lookup] at accepted
      | some blob =>
        simp only [lookup] at accepted
        split at accepted
        · contradiction
        · rename_i valid
          have fields : blob.key = key ∧ blob.bytes.size = count := by simpa using valid
          simp only [List.mem_cons] at member
          rcases member with same | later
          · let file : ValidatedFile := ⟨name, flag, blob.bytes, blob.digest⟩
            refine ⟨file, bindFiles_retains blobs rest _ after accepted file (by simp [file]), ?_⟩
            exact ⟨name, flag, count, key, blob, same, lookup, fields.1, rfl, rfl, rfl, rfl, fields.2⟩
          · exact ih _ after accepted later

def fileNames : List Node → List String
  | [] => []
  | .file path _ _ _ :: rest => path.text :: fileNames rest
  | _ :: rest => fileNames rest

theorem fileNames_member (nodes : List Node) (key : String) (member : key ∈ fileNames nodes) :
    ∃ node ∈ nodes, node.path.text = key := by
  induction nodes with
  | nil => simp [fileNames] at member
  | cons node rest ih =>
    cases node with
    | directory path =>
      obtain ⟨found, present, same⟩ := ih member
      exact ⟨found, List.mem_cons_of_mem _ present, same⟩
    | omitted path =>
      obtain ⟨found, present, same⟩ := ih member
      exact ⟨found, List.mem_cons_of_mem _ present, same⟩
    | file path executable size digest =>
      simp only [fileNames, List.mem_cons] at member
      rcases member with same | later
      · exact ⟨.file path executable size digest, by simp, same.symm⟩
      · obtain ⟨found, present, same⟩ := ih later
        exact ⟨found, List.mem_cons_of_mem _ present, same⟩

theorem fileNames_unique (nodes : List Node)
    (unique : nodes.Pairwise (fun first second => first.path.text ≠ second.path.text)) :
    (fileNames nodes).Nodup := by
  induction nodes with
  | nil => simp [fileNames]
  | cons node rest ih =>
    have properties := List.pairwise_cons.mp unique
    cases node with
    | directory path => exact ih properties.2
    | omitted path => exact ih properties.2
    | file path executable size digest =>
      apply List.nodup_cons.mpr
      refine ⟨?_, ih properties.2⟩
      intro member
      rcases fileNames_member rest path.text member with ⟨found, present, same⟩
      exact properties.1 found present same.symm

theorem bindFiles_names (blobs : BlobState) (nodes : List Node) (before after : BoundFiles)
    (accepted : bindFiles blobs nodes before = .ok after) :
    after.reversed.reverse.map (fun file => file.path.text) =
      before.reversed.reverse.map (fun file => file.path.text) ++ fileNames nodes := by
  induction nodes generalizing before after with
  | nil => cases accepted; simp [fileNames]
  | cons node rest ih =>
    cases node with
    | directory path => exact ih before after accepted
    | omitted path => exact ih before after accepted
    | file path executable size digest =>
      unfold bindFiles at accepted
      dsimp only at accepted
      cases lookup : blobs.index[digest]? with
      | none => simp [lookup] at accepted
      | some blob =>
        simp only [lookup] at accepted
        split at accepted
        · contradiction
        · have names := ih _ after accepted
          simpa only [List.reverse_cons, List.map_append, List.map_singleton, fileNames,
            List.append_assoc, List.singleton_append] using names

theorem node_partition_count (nodes : List Node) :
    (fileNames nodes).length +
      (nodes.filterMap (fun node => match node with | .directory path => some path | _ => none)).length +
      (nodes.filterMap (fun node => match node with | .omitted path => some path | _ => none)).length = nodes.length := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    cases node <;> simp only [fileNames, List.filterMap_cons, List.length_cons] at * <;> omega

theorem node_omitted_count (nodes : List Node) :
    (nodes.filterMap (fun node => match node with | .omitted path => some path | _ => none)).length =
      nodeOmitted nodes := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    cases node <;> simp [nodeOmitted, Node.kind] at * <;> omega

theorem manifest_directory_member (state : ManifestState) (path : ExportPath) (member : path ∈ state.dirs) :
    Node.directory path ∈ state.entries.toList := by
  obtain ⟨node, present, mapped⟩ := List.mem_filterMap.mp member
  cases node <;> simp_all

theorem manifest_omitted_member (state : ManifestState) (path : ExportPath) (member : path ∈ state.omittedPaths) :
    Node.omitted path ∈ state.entries.toList := by
  obtain ⟨node, present, mapped⟩ := List.mem_filterMap.mp member
  cases node <;> simp_all

end LeanCage.Host.Artifacts
