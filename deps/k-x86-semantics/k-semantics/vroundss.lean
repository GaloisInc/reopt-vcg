def vroundss : instruction :=
  definst "vroundss" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 96)) <- eval (extract v_4 0 96);
      let v_6 <- evaluateAddress mem_1;
      let v_7 <- load v_6 4;
      let v_8 <- eval (concat v_5 (/- (_,_) -/  cvt_single_to_int32_rm v_7 (handleImmediateWithSignExtend imm_0 8 8)));
      setRegister (lhs.of_reg xmm_3) v_8;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 96)) <- eval (extract v_4 0 96);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_8 <- eval (concat v_5 (/- (_,_) -/  cvt_single_to_int32_rm v_7 (handleImmediateWithSignExtend imm_0 8 8)));
      setRegister (lhs.of_reg xmm_3) v_8;
      pure ()
     action
