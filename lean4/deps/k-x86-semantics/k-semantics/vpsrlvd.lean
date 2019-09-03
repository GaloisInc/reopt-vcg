def vpsrlvd1 : instruction :=
  definst "vpsrlvd" $ do
    pattern fun (v_3367 : reg (bv 128)) (v_3368 : reg (bv 128)) (v_3369 : reg (bv 128)) => do
      v_9432 <- getRegister v_3368;
      v_9434 <- getRegister v_3367;
      setRegister (lhs.of_reg v_3369) (concat (lshr (extract v_9432 0 32) (uvalueMInt (extract v_9434 0 32))) (concat (lshr (extract v_9432 32 64) (uvalueMInt (extract v_9434 32 64))) (concat (lshr (extract v_9432 64 96) (uvalueMInt (extract v_9434 64 96))) (lshr (extract v_9432 96 128) (uvalueMInt (extract v_9434 96 128))))));
      pure ()
    pat_end;
    pattern fun (v_3378 : reg (bv 256)) (v_3379 : reg (bv 256)) (v_3380 : reg (bv 256)) => do
      v_9459 <- getRegister v_3379;
      v_9461 <- getRegister v_3378;
      setRegister (lhs.of_reg v_3380) (concat (lshr (extract v_9459 0 32) (uvalueMInt (extract v_9461 0 32))) (concat (lshr (extract v_9459 32 64) (uvalueMInt (extract v_9461 32 64))) (concat (lshr (extract v_9459 64 96) (uvalueMInt (extract v_9461 64 96))) (concat (lshr (extract v_9459 96 128) (uvalueMInt (extract v_9461 96 128))) (concat (lshr (extract v_9459 128 160) (uvalueMInt (extract v_9461 128 160))) (concat (lshr (extract v_9459 160 192) (uvalueMInt (extract v_9461 160 192))) (concat (lshr (extract v_9459 192 224) (uvalueMInt (extract v_9461 192 224))) (lshr (extract v_9459 224 256) (uvalueMInt (extract v_9461 224 256))))))))));
      pure ()
    pat_end;
    pattern fun (v_3364 : Mem) (v_3362 : reg (bv 128)) (v_3363 : reg (bv 128)) => do
      v_15741 <- getRegister v_3362;
      v_15743 <- evaluateAddress v_3364;
      v_15744 <- load v_15743 16;
      setRegister (lhs.of_reg v_3363) (concat (lshr (extract v_15741 0 32) (uvalueMInt (extract v_15744 0 32))) (concat (lshr (extract v_15741 32 64) (uvalueMInt (extract v_15744 32 64))) (concat (lshr (extract v_15741 64 96) (uvalueMInt (extract v_15744 64 96))) (lshr (extract v_15741 96 128) (uvalueMInt (extract v_15744 96 128))))));
      pure ()
    pat_end;
    pattern fun (v_3373 : Mem) (v_3374 : reg (bv 256)) (v_3375 : reg (bv 256)) => do
      v_15764 <- getRegister v_3374;
      v_15766 <- evaluateAddress v_3373;
      v_15767 <- load v_15766 32;
      setRegister (lhs.of_reg v_3375) (concat (lshr (extract v_15764 0 32) (uvalueMInt (extract v_15767 0 32))) (concat (lshr (extract v_15764 32 64) (uvalueMInt (extract v_15767 32 64))) (concat (lshr (extract v_15764 64 96) (uvalueMInt (extract v_15767 64 96))) (concat (lshr (extract v_15764 96 128) (uvalueMInt (extract v_15767 96 128))) (concat (lshr (extract v_15764 128 160) (uvalueMInt (extract v_15767 128 160))) (concat (lshr (extract v_15764 160 192) (uvalueMInt (extract v_15767 160 192))) (concat (lshr (extract v_15764 192 224) (uvalueMInt (extract v_15767 192 224))) (lshr (extract v_15764 224 256) (uvalueMInt (extract v_15767 224 256))))))))));
      pure ()
    pat_end
