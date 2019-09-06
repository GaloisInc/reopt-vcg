def vtestps1 : instruction :=
  definst "vtestps" $ do
    pattern fun (v_3190 : reg (bv 128)) (v_3191 : reg (bv 128)) => do
      v_7384 <- getRegister v_3191;
      v_7385 <- getRegister v_3190;
      v_7386 <- eval (bv_and v_7384 v_7385);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_7384 96 97) (expression.bv_nat 1 1)) (extract v_7385 96 97)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_7384 64 65) (expression.bv_nat 1 1)) (extract v_7385 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7384 32 33) (expression.bv_nat 1 1)) (extract v_7385 32 33)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7384 0 1) (expression.bv_nat 1 1)) (extract v_7385 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_7386 96) (isBitClear v_7386 64)) (isBitClear v_7386 32)) (isBitClear v_7386 0));
      pure ()
    pat_end;
    pattern fun (v_3199 : reg (bv 256)) (v_3200 : reg (bv 256)) => do
      v_7427 <- getRegister v_3200;
      v_7428 <- getRegister v_3199;
      v_7429 <- eval (bv_and v_7427 v_7428);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_7427 224 225) (expression.bv_nat 1 1)) (extract v_7428 224 225)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_7427 192 193) (expression.bv_nat 1 1)) (extract v_7428 192 193)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7427 160 161) (expression.bv_nat 1 1)) (extract v_7428 160 161)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7427 128 129) (expression.bv_nat 1 1)) (extract v_7428 128 129)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7427 96 97) (expression.bv_nat 1 1)) (extract v_7428 96 97)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7427 64 65) (expression.bv_nat 1 1)) (extract v_7428 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7427 32 33) (expression.bv_nat 1 1)) (extract v_7428 32 33)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7427 0 1) (expression.bv_nat 1 1)) (extract v_7428 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (isBitClear v_7429 224) (isBitClear v_7429 192)) (isBitClear v_7429 160)) (isBitClear v_7429 128)) (isBitClear v_7429 96)) (isBitClear v_7429 64)) (isBitClear v_7429 32)) (isBitClear v_7429 0));
      pure ()
    pat_end;
    pattern fun (v_3185 : Mem) (v_3186 : reg (bv 128)) => do
      v_13279 <- getRegister v_3186;
      v_13280 <- evaluateAddress v_3185;
      v_13281 <- load v_13280 16;
      v_13282 <- eval (bv_and v_13279 v_13281);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_13279 96 97) (expression.bv_nat 1 1)) (extract v_13281 96 97)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_13279 64 65) (expression.bv_nat 1 1)) (extract v_13281 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13279 32 33) (expression.bv_nat 1 1)) (extract v_13281 32 33)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13279 0 1) (expression.bv_nat 1 1)) (extract v_13281 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_13282 96) (isBitClear v_13282 64)) (isBitClear v_13282 32)) (isBitClear v_13282 0));
      pure ()
    pat_end;
    pattern fun (v_3194 : Mem) (v_3195 : reg (bv 256)) => do
      v_13319 <- getRegister v_3195;
      v_13320 <- evaluateAddress v_3194;
      v_13321 <- load v_13320 32;
      v_13322 <- eval (bv_and v_13319 v_13321);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_13319 224 225) (expression.bv_nat 1 1)) (extract v_13321 224 225)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_13319 192 193) (expression.bv_nat 1 1)) (extract v_13321 192 193)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13319 160 161) (expression.bv_nat 1 1)) (extract v_13321 160 161)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13319 128 129) (expression.bv_nat 1 1)) (extract v_13321 128 129)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13319 96 97) (expression.bv_nat 1 1)) (extract v_13321 96 97)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13319 64 65) (expression.bv_nat 1 1)) (extract v_13321 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13319 32 33) (expression.bv_nat 1 1)) (extract v_13321 32 33)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13319 0 1) (expression.bv_nat 1 1)) (extract v_13321 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (isBitClear v_13322 224) (isBitClear v_13322 192)) (isBitClear v_13322 160)) (isBitClear v_13322 128)) (isBitClear v_13322 96)) (isBitClear v_13322 64)) (isBitClear v_13322 32)) (isBitClear v_13322 0));
      pure ()
    pat_end
