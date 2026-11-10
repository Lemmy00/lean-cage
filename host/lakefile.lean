import Lake
open Lake DSL

-- §AR-host-boundary.organization: One functional package serves the host and shared byte parser.
package leanCageHost where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]

@[default_target]
lean_lib LeanCageHost

-- §AR-host-boundary.acceptance: Track executable-source imports in the ordinary module graph.
lean_lib HostExecutableSource where
  roots := #[`HostMain]

lean_lib HostVerification where
  srcDir := "../verification/host"
  roots := #[`BytesProofs, `JsonProofs, `TransportProofs, `SnapshotProofs, `ArtifactsProofs,
    `RetrievalProofs, `GatewayWordCode, `GatewayRequestCode, `ProgramProofs, `FilesystemContracts,
    `ApplicationProofs, `PublicationProofs, `PolicyProofs, `VirtualMachineProofs, `ReceiveProofs,
    `FilesystemOwnership, `RunDirectoryProofs, `ImageProofs, `ExecutionProofs, `FilesystemWrites,
    `FilesystemPrefixes, `FilesystemPermissions, `PublicationConnection, `RequestGuarantee,
    `CallerProofs, `PacketProofs, `EntrypointProofs, `EntrypointExecutableProofs, `EngineIdentityProofs, `GatewayResponseCode,
    `FilesystemDescriptors, `FilesystemNamespaces, `FilesystemBorrowing, `CommandProofs,
    `FilesystemActors, `FilesystemSourceFrames, `PrefixOrigins, `FilesystemBirths,
    `FilesystemForeign, `FilesystemMarkers, `FilesystemReads, `RunPrefixCuts,
    `PreparationPrefixCuts, `ValidatorPrefixCuts, `CallerPrefixCuts, `RuntimeEffects, `FilesystemRuntime, `FilesystemCapabilities,
    `EntrypointPrefixCuts, `EntrypointWriterPrefix, `EntrypointPendingWriter, `EntrypointChannelWriter, `FilesystemReferences, `FilesystemProjection,
    `FilesystemDirectoryObjects, `FilesystemCreationSources, `FilesystemUses,
    `FilesystemFamilies, `FilesystemLookups, `FilesystemRecording, `FilesystemCwdFrames,
    `FilesystemChanges, `FilesystemSourceKinds, `FilesystemSourceOrigins, `GatewayResponseWords,
    `FilesystemPublicationSource, `FilesystemSpawnSources, `FilesystemProcesses, `ValidationReapingProofs,
    `PublicationCustodyProofs, `FilesystemInitial, `FilesystemDirectorySources, `FilesystemMetadata,
    `VirtualMachineCustodyProofs, `FilesystemRootAuthority, `FilesystemExecFlags, `FilesystemHandoff,
    `PublicationMarkerProofs, `FilesystemMarkerSources, `FilesystemCryptography,
    `FilesystemReadSources, `FilesystemBackend, `FilesystemChildEffects, `FilesystemAuthoritySources,
    `FilesystemGlobalAuthority, `FilesystemAuthenticity, `FilesystemDirectoryHandles, `FilesystemMarkerBindings,
    `FilesystemObjectLifetime, `FilesystemLiveMetadata, `FilesystemMarkerLifetime, `FilesystemMarkerGuards,
    `FilesystemPublicationBorrowing, `FilesystemActorBorrowing, `GatewayBootstrapCode,
    `FilesystemForeignNamespace, `FilesystemParentHandles, `FilesystemPublicationHandles,
    `FilesystemRootRegistration, `FilesystemBoundaries, `FilesystemFamilyAuthority, `FilesystemMkdirSources,
    `FilesystemReferenceLifetime, `FilesystemDirectoryObservations, `FilesystemIntervals, `FilesystemObservedAuthority,
    `FilesystemCommitAuthority, `FilesystemNamespaceState, `FilesystemMkdirOrigins,
    `FilesystemRunMkdirAuthority, `FilesystemPrimitiveSelection,
    `FilesystemPublicDirectory, `FilesystemRootCatalogue, `FilesystemFamilyJournal,
    `FilesystemAccessProofs, `FilesystemLookupSemantics,
    `FilesystemAccessJournal, `FilesystemApplicationLowering,
    `FilesystemNativeOperations, `FilesystemNativeEffects,
    `FilesystemPrimitiveSources,
    `NativeCode, `FilesystemNativeDecoding, `FilesystemNativeBirths, `FilesystemPrimitiveRoles,
    `FilesystemNativeReferences,
    `FilesystemPrimitiveRecording, `FilesystemPrimitiveProbes, `FilesystemLookupNames,
    `FilesystemNativeHandoff, `FilesystemNativeExecutions,
    `FilesystemPrimitiveChunks, `FilesystemPrimitiveObservations,
    `FilesystemPrimitiveFrames, `FilesystemPrimitiveParents,
    `FilesystemGuardBorrowing, `FilesystemLoweringLaws,
    `FilesystemLoweredBorrowing, `FilesystemLoweredPaths, `FilesystemLoweredHistory,
    `FilesystemGuardedOpens, `FilesystemLoweredGuards, `FilesystemLoweredPathGuards, `FilesystemLoweredPhases, `FilesystemLoweredReads, `FilesystemPrimitiveReads, `FilesystemNativeMetadata, `FilesystemNativeAuthority, `FilesystemParentLeases, `FilesystemPrimitivePhases, `FilesystemLoweredDirectories,
    `FilesystemPrimitiveIntervals, `FilesystemPrimitiveParentAuthority,
    `FilesystemLookupAuthority, `FilesystemParentState,
    `FilesystemProbeBounds, `FilesystemParentComparison,
    `FilesystemByteNamespaces,
    `FilesystemCreationDeltas,
    `FilesystemCreationState,
    `FilesystemInitialAnchors,
    `FilesystemAnchorOperations,
    `FilesystemAnchorHistory,
    `FilesystemRunCreation,
    `FilesystemBoundaryComparison,
    `FilesystemLoweredDirectoryBorrowing,
    `FilesystemLoweredParentObservations,
    `FilesystemCheckedParents,
    `FilesystemParentTraversal,
    `FilesystemLoweredPublicationBorrowing,
    `FilesystemDirectoryAliases,
    `FilesystemLoweredAliases,
    `FilesystemPrimitivePublication,
    `FilesystemPathComponents,
    `FilesystemNativeCodeRows,
    `FilesystemNativeForkRows,
    `NativeChannelCode,
    `FilesystemNativeChannelRows,
    `FilesystemNativeExecRows,
    `FilesystemNativeLaunchHistory,
    `FilesystemAcknowledgedBirth,
    `FilesystemRootRegistrationHistory,
    `FilesystemRegisteredCustody, `FilesystemInitialDirectoryCustody, `FilesystemRegisteredPassive,
    `FilesystemRegisteredNative, `FilesystemWriteSources, `EntrypointWriteOrigins, `FilesystemPrimitivePrefixPhases,
    `FilesystemRunningHistory, `FilesystemPendingProgramPhases, `FilesystemPendingPrefixPhases, `FilesystemPendingWrites, `FilesystemChannelWrites, `FilesystemDescriptionOrigins, `FilesystemChannelVM,
    `FilesystemSourceIntervals,
    `FilesystemRootReopen,
    `FilesystemPrimitiveRootOpening,
    `FilesystemRunOpeningSource,
    `FilesystemRunReopen,
    `FilesystemPublicationOpening,
    `FilesystemStagingOpeningSource,
    `FilesystemStagingReopen,
    `FilesystemPublicationContentProfile,
    `FilesystemNativeMarkerLifetime,
    `FilesystemCommittedAuthentication,
    `FilesystemLoweredCryptography,
    `FilesystemRetrievalAuthentication,
    `FilesystemOpenTargets,
    `FilesystemDescriptorEffects,
    `FilesystemPassiveCustody,
    `FilesystemDescendantState,
    `FilesystemDescendantPrefix,
    `FilesystemLaunchPrefix,
    `FilesystemChildOpenSource,
    `FilesystemRemovalJournal,
    `FilesystemOwnershipPrefix, `FilesystemOwnershipCuts, `FilesystemHistoricalRoot, `FilesystemChildOpenObservation, `FilesystemRootOpenReceipt,
    `FilesystemEarlierOpen, `FilesystemCreatedOpening, `FilesystemCreatedStage, `FilesystemSourceNondestructive, `FilesystemStageReference, `FilesystemOpenSourceCut,
    `FilesystemCreationOwnership,
    `FilesystemNativeNamespace,
    `FilesystemNativeCustody,
    `FilesystemCwdCustody,
    `FilesystemPassiveOwnership,
    `FilesystemInheritedPrefix,
    `FilesystemCurrentBirth,
    `FilesystemCustodyState,
    `FilesystemAnchorTargets,
    `FilesystemRetirement,
    `FilesystemBirthScopes,
    `FilesystemCreationStateJoin,
    `FilesystemNamespaceMetadata,
    `FilesystemRetirementProjection,
    `FilesystemNativeRetirement,
    `FilesystemRetirementCustody,
    `FilesystemTraversalAuthority,
    `FilesystemCreationPrefix,
    `FilesystemCustodyPrefix,
    `FilesystemReferenceCustody,
    `FilesystemMkdirRoles,
    `FilesystemTraversalParents,
    `FilesystemPublicParents,
    `FilesystemPublicTraversal,
    `FilesystemHistoricalLookup,
    `FilesystemScopeJournal,
    `FilesystemLoweredPublicStart,
    `FilesystemStagingAuthority,
    `FilesystemStagingParents,
    `FilesystemPublicationCreation,
    `FilesystemLoweredWrites,
    `FilesystemBoundaryAuthority,
    `FilesystemVirtualMachineBorrowing, `GatewaySpawnChannels, `GatewayPrivateStreams, `GatewayStreamSources, `GatewayStreamWriter, `GatewayStreamKernel, `GatewayStreamJournal]

-- §AR-host-boundary.interfaces: One-operation adapters expose the Linux/runtime boundary.
extern_lib hostPrimitives pkg := do
  let source ← inputFile (pkg.dir / ".." / "linux" / "host_primitives.c") true
  let object ← buildO (pkg.buildDir / "native" / "host_primitives.o") source
    #["-I", (← getLeanIncludeDir).toString]
    #["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-fPIC"]
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "host_primitives") #[object]

lean_exe «leancage-host» where
  root := `HostMain
  moreLinkArgs := #["/lib/x86_64-linux-gnu/libcrypto.so.3", "-Wl,--allow-shlib-undefined"]

-- §FS-host-boundary.ownership: Native fixture runs only in its newly created test directory.
lean_exe «source-paths-check» where
  srcDir := "../verification/host"
  root := `SourcePathsNative
  moreLinkArgs := #["/lib/x86_64-linux-gnu/libcrypto.so.3", "-Wl,--allow-shlib-undefined"]

-- §FS-host-boundary.publication: Exercise uncertain commit in a fresh owned fixture.
lean_exe «publication-custody-check» where
  srcDir := "../verification/host"
  root := `PublicationCustodyNative
  moreLinkArgs := #["/lib/x86_64-linux-gnu/libcrypto.so.3", "-Wl,--allow-shlib-undefined"]

-- §FS-host-boundary.ownership: Retain the backing name after an uncertain spawn.
lean_exe «vm-custody-check» where
  srcDir := "../verification/host"
  root := `VirtualMachineCustodyNative
  moreLinkArgs := #["/lib/x86_64-linux-gnu/libcrypto.so.3", "-Wl,--allow-shlib-undefined"]

-- §FS-host-boundary.ownership: Check directory lookup semantics in a fresh owned fixture.
lean_exe «filesystem-access-check» where
  srcDir := "../verification/host"
  root := `FilesystemAccessNative
  moreLinkArgs := #["/lib/x86_64-linux-gnu/libcrypto.so.3", "-Wl,--allow-shlib-undefined"]
