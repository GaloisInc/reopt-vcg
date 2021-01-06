def vmovmskps : instruction :=
  definst "vmovmskps" $ do
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_5 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_6 : expression (bv 1)) <- eval (extract v_2 96 97);
      let v_7 <- eval (concat v_5 v_6);
      let v_8 <- eval (concat v_4 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat (expression.bv_nat 28 0) v_9);
      setRegister (lhs.of_reg r32_1) v_10;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_5 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_6 : expression (bv 1)) <- eval (extract v_2 96 97);
      let v_7 <- eval (concat v_5 v_6);
      let v_8 <- eval (concat v_4 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat (expression.bv_nat 60 0) v_9);
      setRegister (lhs.of_reg r64_1) v_10;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg ymm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_5 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_6 : expression (bv 1)) <- eval (extract v_2 96 97);
      let (v_7 : expression (bv 1)) <- eval (extract v_2 128 129);
      let (v_8 : expression (bv 1)) <- eval (extract v_2 160 161);
      let (v_9 : expression (bv 1)) <- eval (extract v_2 192 193);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 224 225);
      let v_11 <- eval (concat v_9 v_10);
      let v_12 <- eval (concat v_8 v_11);
      let v_13 <- eval (concat v_7 v_12);
      let v_14 <- eval (concat v_6 v_13);
      let v_15 <- eval (concat v_5 v_14);
      let v_16 <- eval (concat v_4 v_15);
      let v_17 <- eval (concat v_3 v_16);
      let v_18 <- eval (concat (expression.bv_nat 24 0) v_17);
      setRegister (lhs.of_reg r32_1) v_18;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg ymm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_5 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_6 : expression (bv 1)) <- eval (extract v_2 96 97);
      let (v_7 : expression (bv 1)) <- eval (extract v_2 128 129);
      let (v_8 : expression (bv 1)) <- eval (extract v_2 160 161);
      let (v_9 : expression (bv 1)) <- eval (extract v_2 192 193);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 224 225);
      let v_11 <- eval (concat v_9 v_10);
      let v_12 <- eval (concat v_8 v_11);
      let v_13 <- eval (concat v_7 v_12);
      let v_14 <- eval (concat v_6 v_13);
      let v_15 <- eval (concat v_5 v_14);
      let v_16 <- eval (concat v_4 v_15);
      let v_17 <- eval (concat v_3 v_16);
      let v_18 <- eval (concat (expression.bv_nat 56 0) v_17);
      setRegister (lhs.of_reg r64_1) v_18;
      pure ()
     action
