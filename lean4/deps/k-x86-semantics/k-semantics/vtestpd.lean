def vtestpd1 : instruction :=
  definst "vtestpd" $ do
    pattern fun (v_3172 : reg (bv 128)) (v_3173 : reg (bv 128)) => do
      v_7314 <- getRegister v_3173;
      v_7315 <- getRegister v_3172;
      v_7316 <- eval (bv_and v_7314 v_7315);
      setRegister af bit_zero;
      setRegister cf (bit_and (eq (bv_and (bv_xor (extract v_7314 64 65) (expression.bv_nat 1 1)) (extract v_7315 64 65)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_7314 0 1) (expression.bv_nat 1 1)) (extract v_7315 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (isBitClear v_7316 64) (isBitClear v_7316 0));
      pure ()
    pat_end;
    pattern fun (v_3181 : reg (bv 256)) (v_3182 : reg (bv 256)) => do
      v_7341 <- getRegister v_3182;
      v_7342 <- getRegister v_3181;
      v_7343 <- eval (bv_and v_7341 v_7342);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_7341 192 193) (expression.bv_nat 1 1)) (extract v_7342 192 193)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_7341 128 129) (expression.bv_nat 1 1)) (extract v_7342 128 129)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7341 64 65) (expression.bv_nat 1 1)) (extract v_7342 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7341 0 1) (expression.bv_nat 1 1)) (extract v_7342 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_7343 192) (isBitClear v_7343 128)) (isBitClear v_7343 64)) (isBitClear v_7343 0));
      pure ()
    pat_end;
    pattern fun (v_3167 : Mem) (v_3168 : reg (bv 128)) => do
      v_13215 <- getRegister v_3168;
      v_13216 <- evaluateAddress v_3167;
      v_13217 <- load v_13216 16;
      v_13218 <- eval (bv_and v_13215 v_13217);
      setRegister af bit_zero;
      setRegister cf (bit_and (eq (bv_and (bv_xor (extract v_13215 64 65) (expression.bv_nat 1 1)) (extract v_13217 64 65)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_13215 0 1) (expression.bv_nat 1 1)) (extract v_13217 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (isBitClear v_13218 64) (isBitClear v_13218 0));
      pure ()
    pat_end;
    pattern fun (v_3176 : Mem) (v_3177 : reg (bv 256)) => do
      v_13239 <- getRegister v_3177;
      v_13240 <- evaluateAddress v_3176;
      v_13241 <- load v_13240 32;
      v_13242 <- eval (bv_and v_13239 v_13241);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_13239 192 193) (expression.bv_nat 1 1)) (extract v_13241 192 193)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_13239 128 129) (expression.bv_nat 1 1)) (extract v_13241 128 129)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13239 64 65) (expression.bv_nat 1 1)) (extract v_13241 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13239 0 1) (expression.bv_nat 1 1)) (extract v_13241 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_13242 192) (isBitClear v_13242 128)) (isBitClear v_13242 64)) (isBitClear v_13242 0));
      pure ()
    pat_end
