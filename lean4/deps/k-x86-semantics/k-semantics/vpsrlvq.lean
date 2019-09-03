def vpsrlvq1 : instruction :=
  definst "vpsrlvq" $ do
    pattern fun (v_3401 : reg (bv 128)) (v_3402 : reg (bv 128)) (v_3403 : reg (bv 128)) => do
      v_9028 <- getRegister v_3402;
      v_9030 <- getRegister v_3401;
      setRegister (lhs.of_reg v_3403) (concat (lshr (extract v_9028 0 64) (uvalueMInt (extract v_9030 0 64))) (lshr (extract v_9028 64 128) (uvalueMInt (extract v_9030 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3413 : reg (bv 256)) (v_3414 : reg (bv 256)) (v_3415 : reg (bv 256)) => do
      v_9045 <- getRegister v_3414;
      v_9047 <- getRegister v_3413;
      setRegister (lhs.of_reg v_3415) (concat (lshr (extract v_9045 0 64) (uvalueMInt (extract v_9047 0 64))) (concat (lshr (extract v_9045 64 128) (uvalueMInt (extract v_9047 64 128))) (concat (lshr (extract v_9045 128 192) (uvalueMInt (extract v_9047 128 192))) (lshr (extract v_9045 192 256) (uvalueMInt (extract v_9047 192 256))))));
      pure ()
    pat_end;
    pattern fun (v_3395 : Mem) (v_3396 : reg (bv 128)) (v_3397 : reg (bv 128)) => do
      v_14919 <- getRegister v_3396;
      v_14921 <- evaluateAddress v_3395;
      v_14922 <- load v_14921 16;
      setRegister (lhs.of_reg v_3397) (concat (lshr (extract v_14919 0 64) (uvalueMInt (extract v_14922 0 64))) (lshr (extract v_14919 64 128) (uvalueMInt (extract v_14922 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3406 : Mem) (v_3408 : reg (bv 256)) (v_3409 : reg (bv 256)) => do
      v_14932 <- getRegister v_3408;
      v_14934 <- evaluateAddress v_3406;
      v_14935 <- load v_14934 32;
      setRegister (lhs.of_reg v_3409) (concat (lshr (extract v_14932 0 64) (uvalueMInt (extract v_14935 0 64))) (concat (lshr (extract v_14932 64 128) (uvalueMInt (extract v_14935 64 128))) (concat (lshr (extract v_14932 128 192) (uvalueMInt (extract v_14935 128 192))) (lshr (extract v_14932 192 256) (uvalueMInt (extract v_14935 192 256))))));
      pure ()
    pat_end
