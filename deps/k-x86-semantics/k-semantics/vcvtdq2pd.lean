def vcvtdq2pd : instruction :=
  definst "vcvtdq2pd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_6 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 53 11) 64) (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 53 11) 64));
      setRegister (lhs.of_reg xmm_1) v_6;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_8 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_6) 53 11) 64) (fp_bitcast_to_bv (Int2Float (svalueMInt v_7) 53 11) 64));
      let v_9 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 53 11) 64) v_8);
      let v_10 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 53 11) 64) v_9);
      setRegister (lhs.of_reg ymm_1) v_10;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_4 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_5 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_3) 53 11) 64) (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 53 11) 64));
      setRegister (lhs.of_reg xmm_1) v_5;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg ymm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 128 160);
      let (v_4 : expression (bv 32)) <- eval (extract v_2 160 192);
      let (v_5 : expression (bv 32)) <- eval (extract v_2 192 224);
      let (v_6 : expression (bv 32)) <- eval (extract v_2 224 256);
      let v_7 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 53 11) 64) (fp_bitcast_to_bv (Int2Float (svalueMInt v_6) 53 11) 64));
      let v_8 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 53 11) 64) v_7);
      let v_9 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_3) 53 11) 64) v_8);
      setRegister (lhs.of_reg ymm_1) v_9;
      pure ()
     action
