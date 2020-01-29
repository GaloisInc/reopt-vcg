def vtestpd : instruction :=
  definst "vtestpd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (bv_and v_2 v_4);
      (v_6 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_7 : expression (bv 1)) <- eval (extract v_4 64 65);
      (v_8 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_9 : expression (bv 1)) <- eval (extract v_4 0 1);
      setRegister af bit_zero;
      setRegister cf (bit_and (eq (bv_and (bv_xor v_6 (expression.bv_nat 1 1)) v_7) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_8 (expression.bv_nat 1 1)) v_9) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (isBitClear v_5 64) (isBitClear v_5 0));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg ymm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- eval (bv_and v_2 v_4);
      (v_6 : expression (bv 1)) <- eval (extract v_2 192 193);
      (v_7 : expression (bv 1)) <- eval (extract v_4 192 193);
      (v_8 : expression (bv 1)) <- eval (extract v_2 128 129);
      (v_9 : expression (bv 1)) <- eval (extract v_4 128 129);
      (v_10 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_11 : expression (bv 1)) <- eval (extract v_4 64 65);
      (v_12 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_13 : expression (bv 1)) <- eval (extract v_4 0 1);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_6 (expression.bv_nat 1 1)) v_7) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_8 (expression.bv_nat 1 1)) v_9) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_10 (expression.bv_nat 1 1)) v_11) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_12 (expression.bv_nat 1 1)) v_13) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_5 192) (isBitClear v_5 128)) (isBitClear v_5 64)) (isBitClear v_5 0));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (bv_and v_2 v_3);
      (v_5 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_6 : expression (bv 1)) <- eval (extract v_3 64 65);
      (v_7 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_8 : expression (bv 1)) <- eval (extract v_3 0 1);
      setRegister af bit_zero;
      setRegister cf (bit_and (eq (bv_and (bv_xor v_5 (expression.bv_nat 1 1)) v_6) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_7 (expression.bv_nat 1 1)) v_8) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (isBitClear v_4 64) (isBitClear v_4 0));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg ymm_1);
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- eval (bv_and v_2 v_3);
      (v_5 : expression (bv 1)) <- eval (extract v_2 192 193);
      (v_6 : expression (bv 1)) <- eval (extract v_3 192 193);
      (v_7 : expression (bv 1)) <- eval (extract v_2 128 129);
      (v_8 : expression (bv 1)) <- eval (extract v_3 128 129);
      (v_9 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_10 : expression (bv 1)) <- eval (extract v_3 64 65);
      (v_11 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_12 : expression (bv 1)) <- eval (extract v_3 0 1);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_5 (expression.bv_nat 1 1)) v_6) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_7 (expression.bv_nat 1 1)) v_8) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_9 (expression.bv_nat 1 1)) v_10) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_11 (expression.bv_nat 1 1)) v_12) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_4 192) (isBitClear v_4 128)) (isBitClear v_4 64)) (isBitClear v_4 0));
      pure ()
    pat_end
