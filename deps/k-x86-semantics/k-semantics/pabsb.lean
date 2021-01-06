def pabsb : instruction :=
  definst "pabsb" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_10 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 56 64);
      let (v_12 : expression (bv 8)) <- eval (extract v_3 64 72);
      let (v_13 : expression (bv 8)) <- eval (extract v_3 72 80);
      let (v_14 : expression (bv 8)) <- eval (extract v_3 80 88);
      let (v_15 : expression (bv 8)) <- eval (extract v_3 88 96);
      let (v_16 : expression (bv 8)) <- eval (extract v_3 96 104);
      let (v_17 : expression (bv 8)) <- eval (extract v_3 104 112);
      let (v_18 : expression (bv 8)) <- eval (extract v_3 112 120);
      let (v_19 : expression (bv 8)) <- eval (extract v_3 120 128);
      let v_20 <- eval (concat (mux (ugt v_18 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_18 (expression.bv_nat 8 255))) v_18) (mux (ugt v_19 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_19 (expression.bv_nat 8 255))) v_19));
      let v_21 <- eval (concat (mux (ugt v_17 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_17 (expression.bv_nat 8 255))) v_17) v_20);
      let v_22 <- eval (concat (mux (ugt v_16 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_16 (expression.bv_nat 8 255))) v_16) v_21);
      let v_23 <- eval (concat (mux (ugt v_15 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_15 (expression.bv_nat 8 255))) v_15) v_22);
      let v_24 <- eval (concat (mux (ugt v_14 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_14 (expression.bv_nat 8 255))) v_14) v_23);
      let v_25 <- eval (concat (mux (ugt v_13 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_13 (expression.bv_nat 8 255))) v_13) v_24);
      let v_26 <- eval (concat (mux (ugt v_12 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_12 (expression.bv_nat 8 255))) v_12) v_25);
      let v_27 <- eval (concat (mux (ugt v_11 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_11 (expression.bv_nat 8 255))) v_11) v_26);
      let v_28 <- eval (concat (mux (ugt v_10 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_10 (expression.bv_nat 8 255))) v_10) v_27);
      let v_29 <- eval (concat (mux (ugt v_9 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9 (expression.bv_nat 8 255))) v_9) v_28);
      let v_30 <- eval (concat (mux (ugt v_8 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_8 (expression.bv_nat 8 255))) v_8) v_29);
      let v_31 <- eval (concat (mux (ugt v_7 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_7 (expression.bv_nat 8 255))) v_7) v_30);
      let v_32 <- eval (concat (mux (ugt v_6 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_6 (expression.bv_nat 8 255))) v_6) v_31);
      let v_33 <- eval (concat (mux (ugt v_5 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5 (expression.bv_nat 8 255))) v_5) v_32);
      let v_34 <- eval (concat (mux (ugt v_4 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_4 (expression.bv_nat 8 255))) v_4) v_33);
      setRegister (lhs.of_reg xmm_1) v_34;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      let (v_4 : expression (bv 8)) <- eval (extract v_2 8 16);
      let (v_5 : expression (bv 8)) <- eval (extract v_2 16 24);
      let (v_6 : expression (bv 8)) <- eval (extract v_2 24 32);
      let (v_7 : expression (bv 8)) <- eval (extract v_2 32 40);
      let (v_8 : expression (bv 8)) <- eval (extract v_2 40 48);
      let (v_9 : expression (bv 8)) <- eval (extract v_2 48 56);
      let (v_10 : expression (bv 8)) <- eval (extract v_2 56 64);
      let (v_11 : expression (bv 8)) <- eval (extract v_2 64 72);
      let (v_12 : expression (bv 8)) <- eval (extract v_2 72 80);
      let (v_13 : expression (bv 8)) <- eval (extract v_2 80 88);
      let (v_14 : expression (bv 8)) <- eval (extract v_2 88 96);
      let (v_15 : expression (bv 8)) <- eval (extract v_2 96 104);
      let (v_16 : expression (bv 8)) <- eval (extract v_2 104 112);
      let (v_17 : expression (bv 8)) <- eval (extract v_2 112 120);
      let (v_18 : expression (bv 8)) <- eval (extract v_2 120 128);
      let v_19 <- eval (concat (mux (ugt v_17 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_17 (expression.bv_nat 8 255))) v_17) (mux (ugt v_18 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_18 (expression.bv_nat 8 255))) v_18));
      let v_20 <- eval (concat (mux (ugt v_16 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_16 (expression.bv_nat 8 255))) v_16) v_19);
      let v_21 <- eval (concat (mux (ugt v_15 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_15 (expression.bv_nat 8 255))) v_15) v_20);
      let v_22 <- eval (concat (mux (ugt v_14 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_14 (expression.bv_nat 8 255))) v_14) v_21);
      let v_23 <- eval (concat (mux (ugt v_13 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_13 (expression.bv_nat 8 255))) v_13) v_22);
      let v_24 <- eval (concat (mux (ugt v_12 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_12 (expression.bv_nat 8 255))) v_12) v_23);
      let v_25 <- eval (concat (mux (ugt v_11 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_11 (expression.bv_nat 8 255))) v_11) v_24);
      let v_26 <- eval (concat (mux (ugt v_10 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_10 (expression.bv_nat 8 255))) v_10) v_25);
      let v_27 <- eval (concat (mux (ugt v_9 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9 (expression.bv_nat 8 255))) v_9) v_26);
      let v_28 <- eval (concat (mux (ugt v_8 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_8 (expression.bv_nat 8 255))) v_8) v_27);
      let v_29 <- eval (concat (mux (ugt v_7 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_7 (expression.bv_nat 8 255))) v_7) v_28);
      let v_30 <- eval (concat (mux (ugt v_6 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_6 (expression.bv_nat 8 255))) v_6) v_29);
      let v_31 <- eval (concat (mux (ugt v_5 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5 (expression.bv_nat 8 255))) v_5) v_30);
      let v_32 <- eval (concat (mux (ugt v_4 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_4 (expression.bv_nat 8 255))) v_4) v_31);
      let v_33 <- eval (concat (mux (ugt v_3 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_3 (expression.bv_nat 8 255))) v_3) v_32);
      setRegister (lhs.of_reg xmm_1) v_33;
      pure ()
     action
