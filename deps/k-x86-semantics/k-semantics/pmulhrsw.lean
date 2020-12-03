def pmulhrsw : instruction :=
  definst "pmulhrsw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let (v_7 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_3 32) (sext v_6 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_8 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_8 32) (sext v_9 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_11 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_13 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_11 32) (sext v_12 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_14 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_16 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_14 32) (sext v_15 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_17 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_19 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_17 32) (sext v_18 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_20 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_21 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_22 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_20 32) (sext v_21 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_23 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_24 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_25 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_23 32) (sext v_24 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_26 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_27 : expression (bv 16)) <- eval (extract v_5 112 128);
      let (v_28 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_26 32) (sext v_27 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let v_29 <- eval (concat v_25 v_28);
      let v_30 <- eval (concat v_22 v_29);
      let v_31 <- eval (concat v_19 v_30);
      let v_32 <- eval (concat v_16 v_31);
      let v_33 <- eval (concat v_13 v_32);
      let v_34 <- eval (concat v_10 v_33);
      let v_35 <- eval (concat v_7 v_34);
      setRegister (lhs.of_reg xmm_1) v_35;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      let (v_6 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_3 32) (sext v_5 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_7 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_7 32) (sext v_8 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_10 32) (sext v_11 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_13 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_14 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_15 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_13 32) (sext v_14 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_16 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_17 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_18 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_16 32) (sext v_17 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_19 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_20 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_21 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_19 32) (sext v_20 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_22 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_23 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_24 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_22 32) (sext v_23 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let (v_25 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_26 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_27 : expression (bv 16)) <- eval (extract (add (lshr (mul (sext v_25 32) (sext v_26 32)) (expression.bv_nat 32 14)) (expression.bv_nat 32 1)) 15 31);
      let v_28 <- eval (concat v_24 v_27);
      let v_29 <- eval (concat v_21 v_28);
      let v_30 <- eval (concat v_18 v_29);
      let v_31 <- eval (concat v_15 v_30);
      let v_32 <- eval (concat v_12 v_31);
      let v_33 <- eval (concat v_9 v_32);
      let v_34 <- eval (concat v_6 v_33);
      setRegister (lhs.of_reg xmm_1) v_34;
      pure ()
     action
