def vtestpd1 : instruction :=
  definst "vtestpd" $ do
    pattern fun (v_3145 : reg (bv 128)) (v_3146 : reg (bv 128)) => do
      v_7287 <- getRegister v_3146;
      v_7288 <- getRegister v_3145;
      v_7289 <- eval (bv_and v_7287 v_7288);
      setRegister af bit_zero;
      setRegister cf (bit_and (eq (bv_and (bv_xor (extract v_7287 64 65) (expression.bv_nat 1 1)) (extract v_7288 64 65)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_7287 0 1) (expression.bv_nat 1 1)) (extract v_7288 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (isBitClear v_7289 64) (isBitClear v_7289 0));
      pure ()
    pat_end;
    pattern fun (v_3154 : reg (bv 256)) (v_3155 : reg (bv 256)) => do
      v_7314 <- getRegister v_3155;
      v_7315 <- getRegister v_3154;
      v_7316 <- eval (bv_and v_7314 v_7315);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_7314 192 193) (expression.bv_nat 1 1)) (extract v_7315 192 193)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_7314 128 129) (expression.bv_nat 1 1)) (extract v_7315 128 129)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7314 64 65) (expression.bv_nat 1 1)) (extract v_7315 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_7314 0 1) (expression.bv_nat 1 1)) (extract v_7315 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_7316 192) (isBitClear v_7316 128)) (isBitClear v_7316 64)) (isBitClear v_7316 0));
      pure ()
    pat_end;
    pattern fun (v_3140 : Mem) (v_3141 : reg (bv 128)) => do
      v_13188 <- getRegister v_3141;
      v_13189 <- evaluateAddress v_3140;
      v_13190 <- load v_13189 16;
      v_13191 <- eval (bv_and v_13188 v_13190);
      setRegister af bit_zero;
      setRegister cf (bit_and (eq (bv_and (bv_xor (extract v_13188 64 65) (expression.bv_nat 1 1)) (extract v_13190 64 65)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_13188 0 1) (expression.bv_nat 1 1)) (extract v_13190 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (isBitClear v_13191 64) (isBitClear v_13191 0));
      pure ()
    pat_end;
    pattern fun (v_3149 : Mem) (v_3150 : reg (bv 256)) => do
      v_13212 <- getRegister v_3150;
      v_13213 <- evaluateAddress v_3149;
      v_13214 <- load v_13213 32;
      v_13215 <- eval (bv_and v_13212 v_13214);
      setRegister af bit_zero;
      setRegister cf (bit_and (bit_and (bit_and (eq (bv_and (bv_xor (extract v_13212 192 193) (expression.bv_nat 1 1)) (extract v_13214 192 193)) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor (extract v_13212 128 129) (expression.bv_nat 1 1)) (extract v_13214 128 129)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13212 64 65) (expression.bv_nat 1 1)) (extract v_13214 64 65)) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor (extract v_13212 0 1) (expression.bv_nat 1 1)) (extract v_13214 0 1)) (expression.bv_nat 1 0)));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (bit_and (bit_and (bit_and (isBitClear v_13215 192) (isBitClear v_13215 128)) (isBitClear v_13215 64)) (isBitClear v_13215 0));
      pure ()
    pat_end
