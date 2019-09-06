def vpsrlvq1 : instruction :=
  definst "vpsrlvq" $ do
    pattern fun (v_3481 : reg (bv 128)) (v_3482 : reg (bv 128)) (v_3483 : reg (bv 128)) => do
      v_8860 <- getRegister v_3482;
      v_8862 <- getRegister v_3481;
      setRegister (lhs.of_reg v_3483) (concat (lshr (extract v_8860 0 64) (extract v_8862 0 64)) (lshr (extract v_8860 64 128) (extract v_8862 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3492 : reg (bv 256)) (v_3493 : reg (bv 256)) (v_3494 : reg (bv 256)) => do
      v_8875 <- getRegister v_3493;
      v_8877 <- getRegister v_3492;
      setRegister (lhs.of_reg v_3494) (concat (lshr (extract v_8875 0 64) (extract v_8877 0 64)) (concat (lshr (extract v_8875 64 128) (extract v_8877 64 128)) (concat (lshr (extract v_8875 128 192) (extract v_8877 128 192)) (lshr (extract v_8875 192 256) (extract v_8877 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3475 : Mem) (v_3476 : reg (bv 128)) (v_3477 : reg (bv 128)) => do
      v_14589 <- getRegister v_3476;
      v_14591 <- evaluateAddress v_3475;
      v_14592 <- load v_14591 16;
      setRegister (lhs.of_reg v_3477) (concat (lshr (extract v_14589 0 64) (extract v_14592 0 64)) (lshr (extract v_14589 64 128) (extract v_14592 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3486 : Mem) (v_3487 : reg (bv 256)) (v_3488 : reg (bv 256)) => do
      v_14600 <- getRegister v_3487;
      v_14602 <- evaluateAddress v_3486;
      v_14603 <- load v_14602 32;
      setRegister (lhs.of_reg v_3488) (concat (lshr (extract v_14600 0 64) (extract v_14603 0 64)) (concat (lshr (extract v_14600 64 128) (extract v_14603 64 128)) (concat (lshr (extract v_14600 128 192) (extract v_14603 128 192)) (lshr (extract v_14600 192 256) (extract v_14603 192 256)))));
      pure ()
    pat_end
