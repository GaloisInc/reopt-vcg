def vpaddq1 : instruction :=
  definst "vpaddq" $ do
    pattern fun (v_3429 : reg (bv 128)) (v_3430 : reg (bv 128)) (v_3431 : reg (bv 128)) => do
      v_7242 <- getRegister v_3430;
      v_7244 <- getRegister v_3429;
      setRegister (lhs.of_reg v_3431) (concat (add (extract v_7242 0 64) (extract v_7244 0 64)) (add (extract v_7242 64 128) (extract v_7244 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3441 : reg (bv 256)) (v_3442 : reg (bv 256)) (v_3443 : reg (bv 256)) => do
      v_7257 <- getRegister v_3442;
      v_7259 <- getRegister v_3441;
      setRegister (lhs.of_reg v_3443) (concat (add (extract v_7257 0 64) (extract v_7259 0 64)) (concat (add (extract v_7257 64 128) (extract v_7259 64 128)) (concat (add (extract v_7257 128 192) (extract v_7259 128 192)) (add (extract v_7257 192 256) (extract v_7259 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3424 : Mem) (v_3425 : reg (bv 128)) (v_3426 : reg (bv 128)) => do
      v_12266 <- getRegister v_3425;
      v_12268 <- evaluateAddress v_3424;
      v_12269 <- load v_12268 16;
      setRegister (lhs.of_reg v_3426) (concat (add (extract v_12266 0 64) (extract v_12269 0 64)) (add (extract v_12266 64 128) (extract v_12269 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3435 : Mem) (v_3436 : reg (bv 256)) (v_3437 : reg (bv 256)) => do
      v_12277 <- getRegister v_3436;
      v_12279 <- evaluateAddress v_3435;
      v_12280 <- load v_12279 32;
      setRegister (lhs.of_reg v_3437) (concat (add (extract v_12277 0 64) (extract v_12280 0 64)) (concat (add (extract v_12277 64 128) (extract v_12280 64 128)) (concat (add (extract v_12277 128 192) (extract v_12280 128 192)) (add (extract v_12277 192 256) (extract v_12280 192 256)))));
      pure ()
    pat_end
