def pmovmskb : instruction :=
  definst "pmovmskb" $ do
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 8 9);
      let (v_5 : expression (bv 1)) <- eval (extract v_2 16 17);
      let (v_6 : expression (bv 1)) <- eval (extract v_2 24 25);
      let (v_7 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_8 : expression (bv 1)) <- eval (extract v_2 40 41);
      let (v_9 : expression (bv 1)) <- eval (extract v_2 48 49);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 56 57);
      let (v_11 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_12 : expression (bv 1)) <- eval (extract v_2 72 73);
      let (v_13 : expression (bv 1)) <- eval (extract v_2 80 81);
      let (v_14 : expression (bv 1)) <- eval (extract v_2 88 89);
      let (v_15 : expression (bv 1)) <- eval (extract v_2 96 97);
      let (v_16 : expression (bv 1)) <- eval (extract v_2 104 105);
      let (v_17 : expression (bv 1)) <- eval (extract v_2 112 113);
      let (v_18 : expression (bv 1)) <- eval (extract v_2 120 121);
      let v_19 <- eval (concat v_17 v_18);
      let v_20 <- eval (concat v_16 v_19);
      let v_21 <- eval (concat v_15 v_20);
      let v_22 <- eval (concat v_14 v_21);
      let v_23 <- eval (concat v_13 v_22);
      let v_24 <- eval (concat v_12 v_23);
      let v_25 <- eval (concat v_11 v_24);
      let v_26 <- eval (concat v_10 v_25);
      let v_27 <- eval (concat v_9 v_26);
      let v_28 <- eval (concat v_8 v_27);
      let v_29 <- eval (concat v_7 v_28);
      let v_30 <- eval (concat v_6 v_29);
      let v_31 <- eval (concat v_5 v_30);
      let v_32 <- eval (concat v_4 v_31);
      let v_33 <- eval (concat v_3 v_32);
      let v_34 <- eval (concat (expression.bv_nat 16 0) v_33);
      setRegister (lhs.of_reg r32_1) v_34;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 8 9);
      let (v_5 : expression (bv 1)) <- eval (extract v_2 16 17);
      let (v_6 : expression (bv 1)) <- eval (extract v_2 24 25);
      let (v_7 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_8 : expression (bv 1)) <- eval (extract v_2 40 41);
      let (v_9 : expression (bv 1)) <- eval (extract v_2 48 49);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 56 57);
      let (v_11 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_12 : expression (bv 1)) <- eval (extract v_2 72 73);
      let (v_13 : expression (bv 1)) <- eval (extract v_2 80 81);
      let (v_14 : expression (bv 1)) <- eval (extract v_2 88 89);
      let (v_15 : expression (bv 1)) <- eval (extract v_2 96 97);
      let (v_16 : expression (bv 1)) <- eval (extract v_2 104 105);
      let (v_17 : expression (bv 1)) <- eval (extract v_2 112 113);
      let (v_18 : expression (bv 1)) <- eval (extract v_2 120 121);
      let v_19 <- eval (concat v_17 v_18);
      let v_20 <- eval (concat v_16 v_19);
      let v_21 <- eval (concat v_15 v_20);
      let v_22 <- eval (concat v_14 v_21);
      let v_23 <- eval (concat v_13 v_22);
      let v_24 <- eval (concat v_12 v_23);
      let v_25 <- eval (concat v_11 v_24);
      let v_26 <- eval (concat v_10 v_25);
      let v_27 <- eval (concat v_9 v_26);
      let v_28 <- eval (concat v_8 v_27);
      let v_29 <- eval (concat v_7 v_28);
      let v_30 <- eval (concat v_6 v_29);
      let v_31 <- eval (concat v_5 v_30);
      let v_32 <- eval (concat v_4 v_31);
      let v_33 <- eval (concat v_3 v_32);
      let v_34 <- eval (concat (expression.bv_nat 48 0) v_33);
      setRegister (lhs.of_reg r64_1) v_34;
      pure ()
     action
