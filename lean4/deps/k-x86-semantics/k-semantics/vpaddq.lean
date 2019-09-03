def vpaddq1 : instruction :=
  definst "vpaddq" $ do
    pattern fun (v_3366 : reg (bv 128)) (v_3367 : reg (bv 128)) (v_3368 : reg (bv 128)) => do
      v_7352 <- getRegister v_3367;
      v_7354 <- getRegister v_3366;
      setRegister (lhs.of_reg v_3368) (concat (add (extract v_7352 0 64) (extract v_7354 0 64)) (add (extract v_7352 64 128) (extract v_7354 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3377 : reg (bv 256)) (v_3378 : reg (bv 256)) (v_3379 : reg (bv 256)) => do
      v_7367 <- getRegister v_3378;
      v_7369 <- getRegister v_3377;
      setRegister (lhs.of_reg v_3379) (concat (add (extract v_7367 0 64) (extract v_7369 0 64)) (concat (add (extract v_7367 64 128) (extract v_7369 64 128)) (concat (add (extract v_7367 128 192) (extract v_7369 128 192)) (add (extract v_7367 192 256) (extract v_7369 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3360 : Mem) (v_3361 : reg (bv 128)) (v_3362 : reg (bv 128)) => do
      v_12568 <- getRegister v_3361;
      v_12570 <- evaluateAddress v_3360;
      v_12571 <- load v_12570 16;
      setRegister (lhs.of_reg v_3362) (concat (add (extract v_12568 0 64) (extract v_12571 0 64)) (add (extract v_12568 64 128) (extract v_12571 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3371 : Mem) (v_3372 : reg (bv 256)) (v_3373 : reg (bv 256)) => do
      v_12579 <- getRegister v_3372;
      v_12581 <- evaluateAddress v_3371;
      v_12582 <- load v_12581 32;
      setRegister (lhs.of_reg v_3373) (concat (add (extract v_12579 0 64) (extract v_12582 0 64)) (concat (add (extract v_12579 64 128) (extract v_12582 64 128)) (concat (add (extract v_12579 128 192) (extract v_12582 128 192)) (add (extract v_12579 192 256) (extract v_12582 192 256)))));
      pure ()
    pat_end
