def vpaddq1 : instruction :=
  definst "vpaddq" $ do
    pattern fun (v_3378 : reg (bv 128)) (v_3379 : reg (bv 128)) (v_3380 : reg (bv 128)) => do
      v_7797 <- getRegister v_3379;
      v_7799 <- getRegister v_3378;
      setRegister (lhs.of_reg v_3380) (concat (add (extract v_7797 0 64) (extract v_7799 0 64)) (add (extract v_7797 64 128) (extract v_7799 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3389 : reg (bv 256)) (v_3390 : reg (bv 256)) (v_3391 : reg (bv 256)) => do
      v_7812 <- getRegister v_3390;
      v_7814 <- getRegister v_3389;
      setRegister (lhs.of_reg v_3391) (concat (add (extract v_7812 0 64) (extract v_7814 0 64)) (concat (add (extract v_7812 64 128) (extract v_7814 64 128)) (concat (add (extract v_7812 128 192) (extract v_7814 128 192)) (add (extract v_7812 192 256) (extract v_7814 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3373 : Mem) (v_3374 : reg (bv 128)) (v_3375 : reg (bv 128)) => do
      v_13445 <- getRegister v_3374;
      v_13447 <- evaluateAddress v_3373;
      v_13448 <- load v_13447 16;
      setRegister (lhs.of_reg v_3375) (concat (add (extract v_13445 0 64) (extract v_13448 0 64)) (add (extract v_13445 64 128) (extract v_13448 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3384 : Mem) (v_3385 : reg (bv 256)) (v_3386 : reg (bv 256)) => do
      v_13456 <- getRegister v_3385;
      v_13458 <- evaluateAddress v_3384;
      v_13459 <- load v_13458 32;
      setRegister (lhs.of_reg v_3386) (concat (add (extract v_13456 0 64) (extract v_13459 0 64)) (concat (add (extract v_13456 64 128) (extract v_13459 64 128)) (concat (add (extract v_13456 128 192) (extract v_13459 128 192)) (add (extract v_13456 192 256) (extract v_13459 192 256)))));
      pure ()
    pat_end
