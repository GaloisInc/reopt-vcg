def vpermps : instruction :=
  definst "vpermps" $ do
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 32;
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 3)) <- eval (extract v_5 29 32);
      let v_7 <- eval (concat (expression.bv_nat 253 0) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract (lshr v_4 (mul v_7 (expression.bv_nat 256 32))) 224 256);
      let (v_9 : expression (bv 3)) <- eval (extract v_5 61 64);
      let v_10 <- eval (concat (expression.bv_nat 253 0) v_9);
      let (v_11 : expression (bv 32)) <- eval (extract (lshr v_4 (mul v_10 (expression.bv_nat 256 32))) 224 256);
      let (v_12 : expression (bv 3)) <- eval (extract v_5 93 96);
      let v_13 <- eval (concat (expression.bv_nat 253 0) v_12);
      let (v_14 : expression (bv 32)) <- eval (extract (lshr v_4 (mul v_13 (expression.bv_nat 256 32))) 224 256);
      let (v_15 : expression (bv 3)) <- eval (extract v_5 125 128);
      let v_16 <- eval (concat (expression.bv_nat 253 0) v_15);
      let (v_17 : expression (bv 32)) <- eval (extract (lshr v_4 (mul v_16 (expression.bv_nat 256 32))) 224 256);
      let (v_18 : expression (bv 3)) <- eval (extract v_5 157 160);
      let v_19 <- eval (concat (expression.bv_nat 253 0) v_18);
      let (v_20 : expression (bv 32)) <- eval (extract (lshr v_4 (mul v_19 (expression.bv_nat 256 32))) 224 256);
      let (v_21 : expression (bv 3)) <- eval (extract v_5 189 192);
      let v_22 <- eval (concat (expression.bv_nat 253 0) v_21);
      let (v_23 : expression (bv 32)) <- eval (extract (lshr v_4 (mul v_22 (expression.bv_nat 256 32))) 224 256);
      let (v_24 : expression (bv 3)) <- eval (extract v_5 221 224);
      let v_25 <- eval (concat (expression.bv_nat 253 0) v_24);
      let (v_26 : expression (bv 32)) <- eval (extract (lshr v_4 (mul v_25 (expression.bv_nat 256 32))) 224 256);
      let (v_27 : expression (bv 3)) <- eval (extract v_5 253 256);
      let v_28 <- eval (concat (expression.bv_nat 253 0) v_27);
      let (v_29 : expression (bv 32)) <- eval (extract (lshr v_4 (mul v_28 (expression.bv_nat 256 32))) 224 256);
      let v_30 <- eval (concat v_26 v_29);
      let v_31 <- eval (concat v_23 v_30);
      let v_32 <- eval (concat v_20 v_31);
      let v_33 <- eval (concat v_17 v_32);
      let v_34 <- eval (concat v_14 v_33);
      let v_35 <- eval (concat v_11 v_34);
      let v_36 <- eval (concat v_8 v_35);
      setRegister (lhs.of_reg ymm_2) v_36;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_0);
      let v_4 <- getRegister (lhs.of_reg ymm_1);
      let (v_5 : expression (bv 3)) <- eval (extract v_4 29 32);
      let v_6 <- eval (concat (expression.bv_nat 253 0) v_5);
      let (v_7 : expression (bv 32)) <- eval (extract (lshr v_3 (mul v_6 (expression.bv_nat 256 32))) 224 256);
      let (v_8 : expression (bv 3)) <- eval (extract v_4 61 64);
      let v_9 <- eval (concat (expression.bv_nat 253 0) v_8);
      let (v_10 : expression (bv 32)) <- eval (extract (lshr v_3 (mul v_9 (expression.bv_nat 256 32))) 224 256);
      let (v_11 : expression (bv 3)) <- eval (extract v_4 93 96);
      let v_12 <- eval (concat (expression.bv_nat 253 0) v_11);
      let (v_13 : expression (bv 32)) <- eval (extract (lshr v_3 (mul v_12 (expression.bv_nat 256 32))) 224 256);
      let (v_14 : expression (bv 3)) <- eval (extract v_4 125 128);
      let v_15 <- eval (concat (expression.bv_nat 253 0) v_14);
      let (v_16 : expression (bv 32)) <- eval (extract (lshr v_3 (mul v_15 (expression.bv_nat 256 32))) 224 256);
      let (v_17 : expression (bv 3)) <- eval (extract v_4 157 160);
      let v_18 <- eval (concat (expression.bv_nat 253 0) v_17);
      let (v_19 : expression (bv 32)) <- eval (extract (lshr v_3 (mul v_18 (expression.bv_nat 256 32))) 224 256);
      let (v_20 : expression (bv 3)) <- eval (extract v_4 189 192);
      let v_21 <- eval (concat (expression.bv_nat 253 0) v_20);
      let (v_22 : expression (bv 32)) <- eval (extract (lshr v_3 (mul v_21 (expression.bv_nat 256 32))) 224 256);
      let (v_23 : expression (bv 3)) <- eval (extract v_4 221 224);
      let v_24 <- eval (concat (expression.bv_nat 253 0) v_23);
      let (v_25 : expression (bv 32)) <- eval (extract (lshr v_3 (mul v_24 (expression.bv_nat 256 32))) 224 256);
      let (v_26 : expression (bv 3)) <- eval (extract v_4 253 256);
      let v_27 <- eval (concat (expression.bv_nat 253 0) v_26);
      let (v_28 : expression (bv 32)) <- eval (extract (lshr v_3 (mul v_27 (expression.bv_nat 256 32))) 224 256);
      let v_29 <- eval (concat v_25 v_28);
      let v_30 <- eval (concat v_22 v_29);
      let v_31 <- eval (concat v_19 v_30);
      let v_32 <- eval (concat v_16 v_31);
      let v_33 <- eval (concat v_13 v_32);
      let v_34 <- eval (concat v_10 v_33);
      let v_35 <- eval (concat v_7 v_34);
      setRegister (lhs.of_reg ymm_2) v_35;
      pure ()
     action
