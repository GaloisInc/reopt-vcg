def roundss : instruction :=
  definst "roundss" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let v_5 <- evaluateAddress mem_1;
      let v_6 <- load v_5 4;
      let v_7 <- eval (concat v_4 (/- (_,_) -/  cvt_single_to_int32_rm v_6 (handleImmediateWithSignExtend imm_0 8 8)));
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_7 <- eval (concat v_4 (/- (_,_) -/  cvt_single_to_int32_rm v_6 (handleImmediateWithSignExtend imm_0 8 8)));
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action
