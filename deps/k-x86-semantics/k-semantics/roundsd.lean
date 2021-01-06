def roundsd : instruction :=
  definst "roundsd" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- evaluateAddress mem_1;
      let v_6 <- load v_5 8;
      let v_7 <- eval (concat v_4 (/- (_,_) -/  cvt_double_to_int64_rm v_6 (handleImmediateWithSignExtend imm_0 8 8)));
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_7 <- eval (concat v_4 (/- (_,_) -/  cvt_double_to_int64_rm v_6 (handleImmediateWithSignExtend imm_0 8 8)));
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action
