def pabsw : instruction :=
  definst "pabsw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_6 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_8 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_12 <- eval (concat (mux (ugt v_10 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10 (expression.bv_nat 16 65535))) v_10) (mux (ugt v_11 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11 (expression.bv_nat 16 65535))) v_11));
      let v_13 <- eval (concat (mux (ugt v_9 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9 (expression.bv_nat 16 65535))) v_9) v_12);
      let v_14 <- eval (concat (mux (ugt v_8 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_8 (expression.bv_nat 16 65535))) v_8) v_13);
      let v_15 <- eval (concat (mux (ugt v_7 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_7 (expression.bv_nat 16 65535))) v_7) v_14);
      let v_16 <- eval (concat (mux (ugt v_6 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6 (expression.bv_nat 16 65535))) v_6) v_15);
      let v_17 <- eval (concat (mux (ugt v_5 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5 (expression.bv_nat 16 65535))) v_5) v_16);
      let v_18 <- eval (concat (mux (ugt v_4 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_4 (expression.bv_nat 16 65535))) v_4) v_17);
      setRegister (lhs.of_reg xmm_1) v_18;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let (v_4 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_5 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_7 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_8 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_11 <- eval (concat (mux (ugt v_9 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9 (expression.bv_nat 16 65535))) v_9) (mux (ugt v_10 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10 (expression.bv_nat 16 65535))) v_10));
      let v_12 <- eval (concat (mux (ugt v_8 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_8 (expression.bv_nat 16 65535))) v_8) v_11);
      let v_13 <- eval (concat (mux (ugt v_7 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_7 (expression.bv_nat 16 65535))) v_7) v_12);
      let v_14 <- eval (concat (mux (ugt v_6 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6 (expression.bv_nat 16 65535))) v_6) v_13);
      let v_15 <- eval (concat (mux (ugt v_5 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5 (expression.bv_nat 16 65535))) v_5) v_14);
      let v_16 <- eval (concat (mux (ugt v_4 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_4 (expression.bv_nat 16 65535))) v_4) v_15);
      let v_17 <- eval (concat (mux (ugt v_3 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_3 (expression.bv_nat 16 65535))) v_3) v_16);
      setRegister (lhs.of_reg xmm_1) v_17;
      pure ()
     action
