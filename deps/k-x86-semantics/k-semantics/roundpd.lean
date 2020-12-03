def roundpd : instruction :=
  definst "roundpd" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      let v_6 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_7 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_8 <- eval (concat (/- (_,_) -/  cvt_double_to_int64_rm v_5 v_6) (/- (_,_) -/  cvt_double_to_int64_rm v_7 v_6));
      setRegister (lhs.of_reg xmm_2) v_8;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_6 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_7 <- eval (concat (/- (_,_) -/  cvt_double_to_int64_rm v_4 v_5) (/- (_,_) -/  cvt_double_to_int64_rm v_6 v_5));
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action
