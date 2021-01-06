def vcvtss2si : instruction :=
  definst "vcvtss2si" $ do
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 4;
      setRegister (lhs.of_reg r32_1) (/- (_) -/ cvt_single_to_int32_truncate v_3);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 4;
      setRegister (lhs.of_reg r64_1) (/- (_) -/ cvt_single_to_int64_truncate v_3);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg r32_1) (/- (_) -/ cvt_single_to_int32_truncate v_3);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg r64_1) (/- (_) -/ cvt_single_to_int64_truncate v_3);
      pure ()
     action
