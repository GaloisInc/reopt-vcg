def roundps : instruction :=
  definst "roundps" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_7 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_10 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_8 v_6) (/- (_,_) -/  cvt_single_to_int32_rm v_9 v_6));
      let v_11 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_7 v_6) v_10);
      let v_12 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_5 v_6) v_11);
      setRegister (lhs.of_reg xmm_2) v_12;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_9 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_7 v_5) (/- (_,_) -/  cvt_single_to_int32_rm v_8 v_5));
      let v_10 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_6 v_5) v_9);
      let v_11 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_4 v_5) v_10);
      setRegister (lhs.of_reg xmm_2) v_11;
      pure ()
     action
