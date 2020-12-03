def vcvtdq2ps : instruction :=
  definst "vcvtdq2ps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_8 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_6) 24 8) 32) (fp_bitcast_to_bv (Int2Float (svalueMInt v_7) 24 8) 32));
      let v_9 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 24 8) 32) v_8);
      let v_10 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 24 8) 32) v_9);
      setRegister (lhs.of_reg xmm_1) v_10;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 32;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 128 160);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 160 192);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 192 224);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_12 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_10) 24 8) 32) (fp_bitcast_to_bv (Int2Float (svalueMInt v_11) 24 8) 32));
      let v_13 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_9) 24 8) 32) v_12);
      let v_14 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_8) 24 8) 32) v_13);
      let v_15 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_7) 24 8) 32) v_14);
      let v_16 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_6) 24 8) 32) v_15);
      let v_17 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 24 8) 32) v_16);
      let v_18 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 24 8) 32) v_17);
      setRegister (lhs.of_reg ymm_1) v_18;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let (v_4 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_5 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_7 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 24 8) 32) (fp_bitcast_to_bv (Int2Float (svalueMInt v_6) 24 8) 32));
      let v_8 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 24 8) 32) v_7);
      let v_9 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_3) 24 8) 32) v_8);
      setRegister (lhs.of_reg xmm_1) v_9;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg ymm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let (v_4 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_5 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      let (v_7 : expression (bv 32)) <- eval (extract v_2 128 160);
      let (v_8 : expression (bv 32)) <- eval (extract v_2 160 192);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 192 224);
      let (v_10 : expression (bv 32)) <- eval (extract v_2 224 256);
      let v_11 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_9) 24 8) 32) (fp_bitcast_to_bv (Int2Float (svalueMInt v_10) 24 8) 32));
      let v_12 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_8) 24 8) 32) v_11);
      let v_13 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_7) 24 8) 32) v_12);
      let v_14 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_6) 24 8) 32) v_13);
      let v_15 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 24 8) 32) v_14);
      let v_16 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 24 8) 32) v_15);
      let v_17 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_3) 24 8) 32) v_16);
      setRegister (lhs.of_reg ymm_1) v_17;
      pure ()
     action
