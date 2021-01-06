def vpabsw : instruction :=
  definst "vpabsw" $ do
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
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 32;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_6 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_8 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_12 : expression (bv 16)) <- eval (extract v_3 128 144);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 144 160);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 160 176);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 176 192);
      let (v_16 : expression (bv 16)) <- eval (extract v_3 192 208);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 208 224);
      let (v_18 : expression (bv 16)) <- eval (extract v_3 224 240);
      let (v_19 : expression (bv 16)) <- eval (extract v_3 240 256);
      let v_20 <- eval (concat (mux (ugt v_18 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_18 (expression.bv_nat 16 65535))) v_18) (mux (ugt v_19 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_19 (expression.bv_nat 16 65535))) v_19));
      let v_21 <- eval (concat (mux (ugt v_17 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_17 (expression.bv_nat 16 65535))) v_17) v_20);
      let v_22 <- eval (concat (mux (ugt v_16 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_16 (expression.bv_nat 16 65535))) v_16) v_21);
      let v_23 <- eval (concat (mux (ugt v_15 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_15 (expression.bv_nat 16 65535))) v_15) v_22);
      let v_24 <- eval (concat (mux (ugt v_14 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_14 (expression.bv_nat 16 65535))) v_14) v_23);
      let v_25 <- eval (concat (mux (ugt v_13 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_13 (expression.bv_nat 16 65535))) v_13) v_24);
      let v_26 <- eval (concat (mux (ugt v_12 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12 (expression.bv_nat 16 65535))) v_12) v_25);
      let v_27 <- eval (concat (mux (ugt v_11 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11 (expression.bv_nat 16 65535))) v_11) v_26);
      let v_28 <- eval (concat (mux (ugt v_10 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10 (expression.bv_nat 16 65535))) v_10) v_27);
      let v_29 <- eval (concat (mux (ugt v_9 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9 (expression.bv_nat 16 65535))) v_9) v_28);
      let v_30 <- eval (concat (mux (ugt v_8 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_8 (expression.bv_nat 16 65535))) v_8) v_29);
      let v_31 <- eval (concat (mux (ugt v_7 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_7 (expression.bv_nat 16 65535))) v_7) v_30);
      let v_32 <- eval (concat (mux (ugt v_6 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6 (expression.bv_nat 16 65535))) v_6) v_31);
      let v_33 <- eval (concat (mux (ugt v_5 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5 (expression.bv_nat 16 65535))) v_5) v_32);
      let v_34 <- eval (concat (mux (ugt v_4 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_4 (expression.bv_nat 16 65535))) v_4) v_33);
      setRegister (lhs.of_reg ymm_1) v_34;
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
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg ymm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let (v_4 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_5 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_7 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_8 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_11 : expression (bv 16)) <- eval (extract v_2 128 144);
      let (v_12 : expression (bv 16)) <- eval (extract v_2 144 160);
      let (v_13 : expression (bv 16)) <- eval (extract v_2 160 176);
      let (v_14 : expression (bv 16)) <- eval (extract v_2 176 192);
      let (v_15 : expression (bv 16)) <- eval (extract v_2 192 208);
      let (v_16 : expression (bv 16)) <- eval (extract v_2 208 224);
      let (v_17 : expression (bv 16)) <- eval (extract v_2 224 240);
      let (v_18 : expression (bv 16)) <- eval (extract v_2 240 256);
      let v_19 <- eval (concat (mux (ugt v_17 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_17 (expression.bv_nat 16 65535))) v_17) (mux (ugt v_18 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_18 (expression.bv_nat 16 65535))) v_18));
      let v_20 <- eval (concat (mux (ugt v_16 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_16 (expression.bv_nat 16 65535))) v_16) v_19);
      let v_21 <- eval (concat (mux (ugt v_15 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_15 (expression.bv_nat 16 65535))) v_15) v_20);
      let v_22 <- eval (concat (mux (ugt v_14 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_14 (expression.bv_nat 16 65535))) v_14) v_21);
      let v_23 <- eval (concat (mux (ugt v_13 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_13 (expression.bv_nat 16 65535))) v_13) v_22);
      let v_24 <- eval (concat (mux (ugt v_12 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12 (expression.bv_nat 16 65535))) v_12) v_23);
      let v_25 <- eval (concat (mux (ugt v_11 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11 (expression.bv_nat 16 65535))) v_11) v_24);
      let v_26 <- eval (concat (mux (ugt v_10 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10 (expression.bv_nat 16 65535))) v_10) v_25);
      let v_27 <- eval (concat (mux (ugt v_9 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9 (expression.bv_nat 16 65535))) v_9) v_26);
      let v_28 <- eval (concat (mux (ugt v_8 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_8 (expression.bv_nat 16 65535))) v_8) v_27);
      let v_29 <- eval (concat (mux (ugt v_7 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_7 (expression.bv_nat 16 65535))) v_7) v_28);
      let v_30 <- eval (concat (mux (ugt v_6 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6 (expression.bv_nat 16 65535))) v_6) v_29);
      let v_31 <- eval (concat (mux (ugt v_5 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5 (expression.bv_nat 16 65535))) v_5) v_30);
      let v_32 <- eval (concat (mux (ugt v_4 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_4 (expression.bv_nat 16 65535))) v_4) v_31);
      let v_33 <- eval (concat (mux (ugt v_3 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_3 (expression.bv_nat 16 65535))) v_3) v_32);
      setRegister (lhs.of_reg ymm_1) v_33;
      pure ()
     action
