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
    `FilesystemRootRetention, `FilesystemCommitRoot, `GatewayFraming,
    `FilesystemCommitRoles, `FilesystemCommitDelta, `FilesystemPublishedCustody,
    `FilesystemPublicationOwnership, `FilesystemCommitCustody,
    `FilesystemCommitMarker, `GatewayChannelHistory, `GatewayChannelBirths, `GatewayChannelPair,
    `FilesystemCustodyExecution, `FilesystemCustodyCuts, `FilesystemCommitInterval,
    `FilesystemPrivateMarker, `FilesystemLifetimePositions, `FilesystemCommitMarkerSurvival,
    `FilesystemCommitExposure, `FilesystemCommitGuarantee, `GatewayChannelReceives,
    `FilesystemRuntimeCustody, `FilesystemUnchangedSource, `FilesystemRootUseAuthority,
    `FilesystemRegisteredDescendants, `FilesystemPrivateReads, `FilesystemRegisteredReopens,
    `FilesystemTemporaryOpen, `FilesystemPublicationRelease, `FilesystemBootstrapOpens,
    `BootstrapProofs, `FilesystemBootstrapSource,
    `FilesystemAllocationReferences, `FilesystemAllocationCustody, `FilesystemExecutableCustody,
    `FilesystemRelativeAllocation, `FilesystemSourceReadForms, `FilesystemSnapshotReadForms,
    `FilesystemReadCustody,
    `FilesystemNativeKeyAccess,
    `SnapshotProofs.Hex, `FilesystemKeyDigest, `FilesystemInstalledAuthentication,
    `FilesystemPrimitiveKeyDigest, `FilesystemCommitAcknowledgement,
    `FilesystemCommittedKeyIdentity, `FilesystemInstalledExposure,
    `FilesystemForeignCustody, `FilesystemPrimitiveBackend, `FilesystemRegisteredLifecycle,
    `FilesystemRecordedAuthority, `FilesystemRecordedBackend, `FilesystemPublicationProgress,
    `PublicationProofs.Frontier, `PublicationProofs.CleanupFrontier,
    `FilesystemPrivateDirectoryOpens, `FilesystemPrivateTraversal, `FilesystemPublicationChains,
    `FilesystemRemovalCustody,
    `PublicationProofs.LoopFrontier, `PublicationProofs.CleanupSource, `FilesystemCleanupParents,
    `FilesystemUnlinkOrigins, `FilesystemCommitPublication,
    `FilesystemPublicationLifecycle, `FilesystemChildCustody, `FilesystemPublicationReads,
    `FilesystemByteNamespaceFrames, `FilesystemPublicationAuthentication, `FilesystemChildLifetimes,
    `FilesystemChildLifetimeCuts, `FilesystemChildReapingSource, `FilesystemChildReapingBinding,
    `VirtualMachineProofs.ReapingSource,
    `FilesystemOutputSources, `FilesystemOutputBorrowing, `FilesystemSnapshotBorrowing,
    `GatewayChannelCode, `GatewayChannelPairSource, `GatewayChannelAliases,
    `GatewayWriterAcknowledgements, `GatewayChannelPairCode,
    `GatewayChannelFlagEffects, `GatewayChannelAliasJournal, `GatewayChannelAuthorityCode,
    `GatewayChannelFlagCode, `GatewayActorCallIdentity, `GatewayWriterReconciliation,
    `GatewayWriterRows, `GatewayChannelSendEntry, `GatewayWriterSynchronization,
    `GatewayStreamSynchronization, `GatewayStreamExtents,
    `GatewayResponseCommitments, `GatewayWriterActiveKeys,
    `GatewayWriterActorAlignment, `GatewayWriterSourceAdvance, `GatewayWriterSynchronizationComplete,
    `GatewayWriterCursor, `GatewayStreamReadRows, `GatewayStreamKeyAccounting,
    `GatewayWriterReturnedOrdinal, `GatewayWriterReturnedAdvance, `GatewayWriterReturnedExecution,
    `GatewayWriterRegistration, `GatewayStreamSourceRegistration, `GatewayWriterRowProducer,
    `GatewayActorLaunchIdentity, `GatewayResponseAckSources, `GatewayStreamCuts, `GatewayResponseAckBytes,
    `FilesystemVmReapingBinding, `FilesystemCreatedRun, `CallerBootstrapSelection,
    `FilesystemRunReference, `RunDirectoryProofs.CleanupFrontier, `FilesystemRunCleanupReference,
    `GatewayWriterCommitOrder, `GatewayStreamGrouping, `GatewayChannelSourceFlags,
    `GatewayChannelReferences, `GatewayChannelReadJournal,
    `GatewayStreamEngineChunks, `GatewayChannelProcessHistory, `GatewayChannelDescriptorEffects,
    `GatewayChannelDiscards, `GatewayChannelPendingBirth,
    `GatewayChannelWriteSources, `GatewayStreamCommitSources,
    `GatewayResponseSourceBounds, `GatewayResponseWriterPrefix, `GatewayChannelResponsePrefix,
    `GatewayChannelReadSelection, `GatewayChannelReceiveUse, `GatewayPendingWriterRegistration,
    `GatewayChannelExternalOperands,
    `GatewayChannelResidualEffects, `GatewayChannelResidualBatch,
    `GatewayFileReadProfile, `GatewayStoredReadProfile, `GatewayPublicationReadProfile,
    `GatewayApplicationReadSources, `GatewayEntrypointReadSources, `GatewayStreamReadSources,
    `GatewayChannelDescriptionLifetimes, `GatewayChannelOFDReferences,
    `GatewayChannelEngineLaunches, `GatewayChannelEngineAbsence,
    `GatewayChannelEngineFamily, `GatewayChannelEngineSource,
    `GatewayChannelEngineReaders, `GatewayChannelReferenceHistory,
    `GatewayChannelReceiveLifetime, `GatewayChannelSocketSurvival,
    `GatewayChannelOFDResidual, `GatewayChannelResidualSources,
    `GatewayChannelSourceJournal, `GatewayChannelSourcePrefix,
    `FilesystemRunCustody, `FilesystemRunUnlink,
    `FilesystemBorrowedOccurrences, `FilesystemCleanupUses, `FilesystemCleanupOccurrences,
    `FilesystemCleanupHistory, `FilesystemOwnershipRetention, `FilesystemRunBoundary,
    `FilesystemRunRemoval,
    `RunDirectoryProofs.SetupCleanup, `FilesystemRunSetupRemoval,
    `FilesystemRunCleanup, `FilesystemJointLifecycle, `FilesystemJointCommit, `PositionalReadProofs,
    `FilesystemPositionedContents,
    `FilesystemBoundedContents,
    `FilesystemBootstrapManifest,
    `FilesystemInstalledEngine,
    `FilesystemJointReads, `FilesystemJointPassive, `FilesystemPublicationCleanupSource,
    `FilesystemCleanupStage, `FilesystemCleanupStageReferences, `FilesystemCleanupBorrowing,
    `FilesystemPendingBorrowing, `FilesystemCleanupStageSegment, `FilesystemCleanupTraversal,
    `FilesystemCleanupAuthority, `FilesystemCleanupCaptured, `FilesystemCleanupReplyOwnership,
    `FilesystemCleanupBeforeRoot, `FilesystemCleanupFinalHistory, `FilesystemCleanupLeading,
    `FilesystemCleanupRootBoundary, `FilesystemPublicationCleanupJoint,
    `FilesystemCleanupObservations, `FilesystemCleanupObservationSource,
    `FilesystemJointUnlinks, `FilesystemJointCreation, `FilesystemJointDescendants,
    `FilesystemPrimitiveBeforePhases, `FilesystemPublicationPreparing,
    `FilesystemPreparingStage, `FilesystemPreparingStageReferences, `FilesystemPreparingReferences,
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

-- §FS-host-boundary.ownership: Close only the directory cursor's checked retained FD.
lean_exe «directory-close-check» where
  srcDir := "../verification/host"
  root := `DirectoryCloseNative
  moreLinkArgs := #["/lib/x86_64-linux-gnu/libcrypto.so.3", "-Wl,--allow-shlib-undefined"]

-- §FS-host-boundary.snapshot: Copy against explicit offsets despite an advanced shared cursor.
lean_exe «positional-copy-check» where
  srcDir := "../verification/host"
  root := `PositionalCopyNative
  moreLinkArgs := #["/lib/x86_64-linux-gnu/libcrypto.so.3", "-Wl,--allow-shlib-undefined"]
