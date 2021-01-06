def vroundpd : instruction :=
  definst "vroundpd" $ do
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
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 32;
      let (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      let v_6 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_7 : expression (bv 64)) <- eval (extract v_4 64 128);
      let (v_8 : expression (bv 64)) <- eval (extract v_4 128 192);
      let (v_9 : expression (bv 64)) <- eval (extract v_4 192 256);
      let v_10 <- eval (concat (/- (_,_) -/  cvt_double_to_int64_rm v_8 v_6) (/- (_,_) -/  cvt_double_to_int64_rm v_9 v_6));
      let v_11 <- eval (concat (/- (_,_) -/  cvt_double_to_int64_rm v_7 v_6) v_10);
      let v_12 <- eval (concat (/- (_,_) -/  cvt_double_to_int64_rm v_5 v_6) v_11);
      setRegister (lhs.of_reg ymm_2) v_12;
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
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_6 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_7 : expression (bv 64)) <- eval (extract v_3 128 192);
      let (v_8 : expression (bv 64)) <- eval (extract v_3 192 256);
      let v_9 <- eval (concat (/- (_,_) -/  cvt_double_to_int64_rm v_7 v_5) (/- (_,_) -/  cvt_double_to_int64_rm v_8 v_5));
      let v_10 <- eval (concat (/- (_,_) -/  cvt_double_to_int64_rm v_6 v_5) v_9);
      let v_11 <- eval (concat (/- (_,_) -/  cvt_double_to_int64_rm v_4 v_5) v_10);
      setRegister (lhs.of_reg ymm_2) v_11;
      pure ()
     action
