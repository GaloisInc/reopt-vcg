def vmovmskpd : instruction :=
  definst "vmovmskpd" $ do
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 64 65);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat (expression.bv_nat 30 0) v_5);
      setRegister (lhs.of_reg r32_1) v_6;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 64 65);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat (expression.bv_nat 62 0) v_5);
      setRegister (lhs.of_reg r64_1) v_6;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg ymm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 64 65);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat (expression.bv_nat 7 0) v_5);
      let (v_7 : expression (bv 8)) <- eval (extract (add v_6 v_6) 1 9);
      let v_8 <- eval (concat (expression.bv_nat 1 0) v_7);
      let (v_9 : expression (bv 1)) <- eval (extract v_2 128 129);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 192 193);
      let v_11 <- eval (concat v_9 v_10);
      let v_12 <- eval (concat (expression.bv_nat 7 0) v_11);
      let (v_13 : expression (bv 8)) <- eval (extract (add v_8 v_12) 1 9);
      let v_14 <- eval (concat (expression.bv_nat 9 0) v_13);
      let v_15 <- eval (concat (expression.bv_nat 9 0) v_7);
      let (v_16 : expression (bv 16)) <- eval (extract (add v_14 v_15) 1 17);
      let v_17 <- eval (concat (expression.bv_nat 16 0) v_16);
      setRegister (lhs.of_reg r32_1) v_17;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg ymm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 64 65);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat (expression.bv_nat 7 0) v_5);
      let (v_7 : expression (bv 8)) <- eval (extract (add v_6 v_6) 1 9);
      let v_8 <- eval (concat (expression.bv_nat 1 0) v_7);
      let (v_9 : expression (bv 1)) <- eval (extract v_2 128 129);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 192 193);
      let v_11 <- eval (concat v_9 v_10);
      let v_12 <- eval (concat (expression.bv_nat 7 0) v_11);
      let (v_13 : expression (bv 8)) <- eval (extract (add v_8 v_12) 1 9);
      let v_14 <- eval (concat (expression.bv_nat 9 0) v_13);
      let v_15 <- eval (concat (expression.bv_nat 9 0) v_7);
      let (v_16 : expression (bv 16)) <- eval (extract (add v_14 v_15) 1 17);
      let v_17 <- eval (concat (expression.bv_nat 48 0) v_16);
      setRegister (lhs.of_reg r64_1) v_17;
      pure ()
     action
