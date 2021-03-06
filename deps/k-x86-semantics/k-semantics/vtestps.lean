def vtestps : instruction :=
  definst "vtestps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let v_5 <- eval (bv_and v_2 v_4);
      let (v_6 : expression (bv 1)) <- eval (extract v_2 96 97);
      let (v_7 : expression (bv 1)) <- eval (extract v_4 96 97);
      let (v_8 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_9 : expression (bv 1)) <- eval (extract v_4 64 65);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_11 : expression (bv 1)) <- eval (extract v_4 32 33);
      let (v_12 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_13 : expression (bv 1)) <- eval (extract v_4 0 1);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_6 (expression.bv_nat 1 1)) v_7) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_8 (expression.bv_nat 1 1)) v_9) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_10 (expression.bv_nat 1 1)) v_11) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_12 (expression.bv_nat 1 1)) v_13) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_5 96) (isBitClear v_5 64)) (isBitClear v_5 32)) (isBitClear v_5 0));
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg ymm_1);
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 32;
      let v_5 <- eval (bv_and v_2 v_4);
      let (v_6 : expression (bv 1)) <- eval (extract v_2 224 225);
      let (v_7 : expression (bv 1)) <- eval (extract v_4 224 225);
      let (v_8 : expression (bv 1)) <- eval (extract v_2 192 193);
      let (v_9 : expression (bv 1)) <- eval (extract v_4 192 193);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 160 161);
      let (v_11 : expression (bv 1)) <- eval (extract v_4 160 161);
      let (v_12 : expression (bv 1)) <- eval (extract v_2 128 129);
      let (v_13 : expression (bv 1)) <- eval (extract v_4 128 129);
      let (v_14 : expression (bv 1)) <- eval (extract v_2 96 97);
      let (v_15 : expression (bv 1)) <- eval (extract v_4 96 97);
      let (v_16 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_17 : expression (bv 1)) <- eval (extract v_4 64 65);
      let (v_18 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_19 : expression (bv 1)) <- eval (extract v_4 32 33);
      let (v_20 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_21 : expression (bv 1)) <- eval (extract v_4 0 1);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_6 (expression.bv_nat 1 1)) v_7) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_8 (expression.bv_nat 1 1)) v_9) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_10 (expression.bv_nat 1 1)) v_11) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_12 (expression.bv_nat 1 1)) v_13) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_14 (expression.bv_nat 1 1)) v_15) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_16 (expression.bv_nat 1 1)) v_17) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_18 (expression.bv_nat 1 1)) v_19) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_20 (expression.bv_nat 1 1)) v_21) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (isBitClear v_5 224) (isBitClear v_5 192)) (isBitClear v_5 160)) (isBitClear v_5 128)) (isBitClear v_5 96)) (isBitClear v_5 64)) (isBitClear v_5 32)) (isBitClear v_5 0));
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let v_4 <- eval (bv_and v_2 v_3);
      let (v_5 : expression (bv 1)) <- eval (extract v_2 96 97);
      let (v_6 : expression (bv 1)) <- eval (extract v_3 96 97);
      let (v_7 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_8 : expression (bv 1)) <- eval (extract v_3 64 65);
      let (v_9 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_10 : expression (bv 1)) <- eval (extract v_3 32 33);
      let (v_11 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_12 : expression (bv 1)) <- eval (extract v_3 0 1);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_5 (expression.bv_nat 1 1)) v_6) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_7 (expression.bv_nat 1 1)) v_8) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_9 (expression.bv_nat 1 1)) v_10) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_11 (expression.bv_nat 1 1)) v_12) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_4 96) (isBitClear v_4 64)) (isBitClear v_4 32)) (isBitClear v_4 0));
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg ymm_1);
      let v_3 <- getRegister (lhs.of_reg ymm_0);
      let v_4 <- eval (bv_and v_2 v_3);
      let (v_5 : expression (bv 1)) <- eval (extract v_2 224 225);
      let (v_6 : expression (bv 1)) <- eval (extract v_3 224 225);
      let (v_7 : expression (bv 1)) <- eval (extract v_2 192 193);
      let (v_8 : expression (bv 1)) <- eval (extract v_3 192 193);
      let (v_9 : expression (bv 1)) <- eval (extract v_2 160 161);
      let (v_10 : expression (bv 1)) <- eval (extract v_3 160 161);
      let (v_11 : expression (bv 1)) <- eval (extract v_2 128 129);
      let (v_12 : expression (bv 1)) <- eval (extract v_3 128 129);
      let (v_13 : expression (bv 1)) <- eval (extract v_2 96 97);
      let (v_14 : expression (bv 1)) <- eval (extract v_3 96 97);
      let (v_15 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_16 : expression (bv 1)) <- eval (extract v_3 64 65);
      let (v_17 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_18 : expression (bv 1)) <- eval (extract v_3 32 33);
      let (v_19 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_20 : expression (bv 1)) <- eval (extract v_3 0 1);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_5 (expression.bv_nat 1 1)) v_6) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_7 (expression.bv_nat 1 1)) v_8) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_9 (expression.bv_nat 1 1)) v_10) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_11 (expression.bv_nat 1 1)) v_12) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_13 (expression.bv_nat 1 1)) v_14) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_15 (expression.bv_nat 1 1)) v_16) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_17 (expression.bv_nat 1 1)) v_18) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_19 (expression.bv_nat 1 1)) v_20) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (isBitClear v_4 224) (isBitClear v_4 192)) (isBitClear v_4 160)) (isBitClear v_4 128)) (isBitClear v_4 96)) (isBitClear v_4 64)) (isBitClear v_4 32)) (isBitClear v_4 0));
      pure ()
     action
