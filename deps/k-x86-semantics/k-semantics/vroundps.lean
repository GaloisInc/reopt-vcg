def vroundps : instruction :=
  definst "vroundps" $ do
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
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 32;
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_7 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_10 : expression (bv 32)) <- eval (extract v_4 128 160);
      let (v_11 : expression (bv 32)) <- eval (extract v_4 160 192);
      let (v_12 : expression (bv 32)) <- eval (extract v_4 192 224);
      let (v_13 : expression (bv 32)) <- eval (extract v_4 224 256);
      let v_14 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_12 v_6) (/- (_,_) -/  cvt_single_to_int32_rm v_13 v_6));
      let v_15 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_11 v_6) v_14);
      let v_16 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_10 v_6) v_15);
      let v_17 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_9 v_6) v_16);
      let v_18 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_8 v_6) v_17);
      let v_19 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_7 v_6) v_18);
      let v_20 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_5 v_6) v_19);
      setRegister (lhs.of_reg ymm_2) v_20;
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
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 128 160);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 160 192);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 192 224);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_13 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_11 v_5) (/- (_,_) -/  cvt_single_to_int32_rm v_12 v_5));
      let v_14 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_10 v_5) v_13);
      let v_15 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_9 v_5) v_14);
      let v_16 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_8 v_5) v_15);
      let v_17 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_7 v_5) v_16);
      let v_18 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_6 v_5) v_17);
      let v_19 <- eval (concat (/- (_,_) -/  cvt_single_to_int32_rm v_4 v_5) v_18);
      setRegister (lhs.of_reg ymm_2) v_19;
      pure ()
     action
