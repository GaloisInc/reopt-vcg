def vpsrlvq1 : instruction :=
  definst "vpsrlvq" $ do
    pattern fun (v_3389 : reg (bv 128)) (v_3390 : reg (bv 128)) (v_3391 : reg (bv 128)) => do
      v_9506 <- getRegister v_3390;
      v_9508 <- getRegister v_3389;
      setRegister (lhs.of_reg v_3391) (concat (lshr (extract v_9506 0 64) (uvalueMInt (extract v_9508 0 64))) (lshr (extract v_9506 64 128) (uvalueMInt (extract v_9508 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3400 : reg (bv 256)) (v_3401 : reg (bv 256)) (v_3402 : reg (bv 256)) => do
      v_9523 <- getRegister v_3401;
      v_9525 <- getRegister v_3400;
      setRegister (lhs.of_reg v_3402) (concat (lshr (extract v_9523 0 64) (uvalueMInt (extract v_9525 0 64))) (concat (lshr (extract v_9523 64 128) (uvalueMInt (extract v_9525 64 128))) (concat (lshr (extract v_9523 128 192) (uvalueMInt (extract v_9525 128 192))) (lshr (extract v_9523 192 256) (uvalueMInt (extract v_9525 192 256))))));
      pure ()
    pat_end;
    pattern fun (v_3386 : Mem) (v_3384 : reg (bv 128)) (v_3385 : reg (bv 128)) => do
      v_15807 <- getRegister v_3384;
      v_15809 <- evaluateAddress v_3386;
      v_15810 <- load v_15809 16;
      setRegister (lhs.of_reg v_3385) (concat (lshr (extract v_15807 0 64) (uvalueMInt (extract v_15810 0 64))) (lshr (extract v_15807 64 128) (uvalueMInt (extract v_15810 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3395 : Mem) (v_3396 : reg (bv 256)) (v_3397 : reg (bv 256)) => do
      v_15820 <- getRegister v_3396;
      v_15822 <- evaluateAddress v_3395;
      v_15823 <- load v_15822 32;
      setRegister (lhs.of_reg v_3397) (concat (lshr (extract v_15820 0 64) (uvalueMInt (extract v_15823 0 64))) (concat (lshr (extract v_15820 64 128) (uvalueMInt (extract v_15823 64 128))) (concat (lshr (extract v_15820 128 192) (uvalueMInt (extract v_15823 128 192))) (lshr (extract v_15820 192 256) (uvalueMInt (extract v_15823 192 256))))));
      pure ()
    pat_end
