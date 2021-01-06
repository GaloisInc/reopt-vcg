def bswap : instruction :=
  definst "bswap" $ do
    instr_pat $ fun (r32_0 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r32_0);
      let (v_2 : expression (bv 8)) <- eval (extract v_1 24 32);
      let (v_3 : expression (bv 8)) <- eval (extract v_1 16 24);
      let v_4 <- eval (concat v_2 v_3);
      let (v_5 : expression (bv 8)) <- eval (extract v_1 8 16);
      let (v_6 : expression (bv 8)) <- eval (extract v_1 0 8);
      let v_7 <- eval (concat v_5 v_6);
      let v_8 <- eval (concat v_4 v_7);
      setRegister (lhs.of_reg r32_0) v_8;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r64_0);
      let (v_2 : expression (bv 8)) <- eval (extract v_1 56 64);
      let (v_3 : expression (bv 8)) <- eval (extract v_1 48 56);
      let v_4 <- eval (concat v_2 v_3);
      let (v_5 : expression (bv 8)) <- eval (extract v_1 40 48);
      let (v_6 : expression (bv 8)) <- eval (extract v_1 32 40);
      let v_7 <- eval (concat v_5 v_6);
      let v_8 <- eval (concat v_4 v_7);
      let (v_9 : expression (bv 8)) <- eval (extract v_1 24 32);
      let (v_10 : expression (bv 8)) <- eval (extract v_1 16 24);
      let v_11 <- eval (concat v_9 v_10);
      let (v_12 : expression (bv 8)) <- eval (extract v_1 8 16);
      let (v_13 : expression (bv 8)) <- eval (extract v_1 0 8);
      let v_14 <- eval (concat v_12 v_13);
      let v_15 <- eval (concat v_11 v_14);
      let v_16 <- eval (concat v_8 v_15);
      setRegister (lhs.of_reg r64_0) v_16;
      pure ()
     action
