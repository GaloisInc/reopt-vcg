def vtestps1 : instruction :=
  definst "vtestps" $ do
    pattern fun (v_3163 : reg (bv 128)) (v_3164 : reg (bv 128)) => do
      v_7357 <- getRegister v_3164;
      v_7358 <- getRegister v_3163;
      v_7359 <- eval (bv_and v_7357 v_7358);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_7357 96 97) (expression.bv_nat 1 1)) (extract v_7358 96 97)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_7357 64 65) (expression.bv_nat 1 1)) (extract v_7358 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7357 32 33) (expression.bv_nat 1 1)) (extract v_7358 32 33)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7357 0 1) (expression.bv_nat 1 1)) (extract v_7358 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_7359 96) (isBitClear v_7359 64)) (isBitClear v_7359 32)) (isBitClear v_7359 0));
      pure ()
    pat_end;
    pattern fun (v_3172 : reg (bv 256)) (v_3173 : reg (bv 256)) => do
      v_7400 <- getRegister v_3173;
      v_7401 <- getRegister v_3172;
      v_7402 <- eval (bv_and v_7400 v_7401);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_7400 224 225) (expression.bv_nat 1 1)) (extract v_7401 224 225)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_7400 192 193) (expression.bv_nat 1 1)) (extract v_7401 192 193)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7400 160 161) (expression.bv_nat 1 1)) (extract v_7401 160 161)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7400 128 129) (expression.bv_nat 1 1)) (extract v_7401 128 129)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7400 96 97) (expression.bv_nat 1 1)) (extract v_7401 96 97)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7400 64 65) (expression.bv_nat 1 1)) (extract v_7401 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7400 32 33) (expression.bv_nat 1 1)) (extract v_7401 32 33)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7400 0 1) (expression.bv_nat 1 1)) (extract v_7401 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (isBitClear v_7402 224) (isBitClear v_7402 192)) (isBitClear v_7402 160)) (isBitClear v_7402 128)) (isBitClear v_7402 96)) (isBitClear v_7402 64)) (isBitClear v_7402 32)) (isBitClear v_7402 0));
      pure ()
    pat_end;
    pattern fun (v_3158 : Mem) (v_3159 : reg (bv 128)) => do
      v_13252 <- getRegister v_3159;
      v_13253 <- evaluateAddress v_3158;
      v_13254 <- load v_13253 16;
      v_13255 <- eval (bv_and v_13252 v_13254);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_13252 96 97) (expression.bv_nat 1 1)) (extract v_13254 96 97)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_13252 64 65) (expression.bv_nat 1 1)) (extract v_13254 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13252 32 33) (expression.bv_nat 1 1)) (extract v_13254 32 33)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13252 0 1) (expression.bv_nat 1 1)) (extract v_13254 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_13255 96) (isBitClear v_13255 64)) (isBitClear v_13255 32)) (isBitClear v_13255 0));
      pure ()
    pat_end;
    pattern fun (v_3167 : Mem) (v_3168 : reg (bv 256)) => do
      v_13292 <- getRegister v_3168;
      v_13293 <- evaluateAddress v_3167;
      v_13294 <- load v_13293 32;
      v_13295 <- eval (bv_and v_13292 v_13294);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_13292 224 225) (expression.bv_nat 1 1)) (extract v_13294 224 225)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_13292 192 193) (expression.bv_nat 1 1)) (extract v_13294 192 193)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13292 160 161) (expression.bv_nat 1 1)) (extract v_13294 160 161)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13292 128 129) (expression.bv_nat 1 1)) (extract v_13294 128 129)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13292 96 97) (expression.bv_nat 1 1)) (extract v_13294 96 97)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13292 64 65) (expression.bv_nat 1 1)) (extract v_13294 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13292 32 33) (expression.bv_nat 1 1)) (extract v_13294 32 33)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13292 0 1) (expression.bv_nat 1 1)) (extract v_13294 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (isBitClear v_13295 224) (isBitClear v_13295 192)) (isBitClear v_13295 160)) (isBitClear v_13295 128)) (isBitClear v_13295 96)) (isBitClear v_13295 64)) (isBitClear v_13295 32)) (isBitClear v_13295 0));
      pure ()
    pat_end
