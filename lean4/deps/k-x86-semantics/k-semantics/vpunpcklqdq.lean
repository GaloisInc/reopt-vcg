def vpunpcklqdq1 : instruction :=
  definst "vpunpcklqdq" $ do
    pattern fun (v_2803 : reg (bv 128)) (v_2804 : reg (bv 128)) (v_2805 : reg (bv 128)) => do
      v_6480 <- getRegister v_2803;
      v_6482 <- getRegister v_2804;
      setRegister (lhs.of_reg v_2805) (concat (extract v_6480 64 128) (extract v_6482 64 128));
      pure ()
    pat_end;
    pattern fun (v_2814 : reg (bv 256)) (v_2815 : reg (bv 256)) (v_2816 : reg (bv 256)) => do
      v_6491 <- getRegister v_2814;
      v_6493 <- getRegister v_2815;
      setRegister (lhs.of_reg v_2816) (concat (concat (extract v_6491 64 128) (extract v_6493 64 128)) (concat (extract v_6491 192 256) (extract v_6493 192 256)));
      pure ()
    pat_end;
    pattern fun (v_2797 : Mem) (v_2798 : reg (bv 128)) (v_2799 : reg (bv 128)) => do
      v_12522 <- evaluateAddress v_2797;
      v_12523 <- load v_12522 16;
      v_12525 <- getRegister v_2798;
      setRegister (lhs.of_reg v_2799) (concat (extract v_12523 64 128) (extract v_12525 64 128));
      pure ()
    pat_end;
    pattern fun (v_2808 : Mem) (v_2809 : reg (bv 256)) (v_2810 : reg (bv 256)) => do
      v_12529 <- evaluateAddress v_2808;
      v_12530 <- load v_12529 32;
      v_12532 <- getRegister v_2809;
      setRegister (lhs.of_reg v_2810) (concat (concat (extract v_12530 64 128) (extract v_12532 64 128)) (concat (extract v_12530 192 256) (extract v_12532 192 256)));
      pure ()
    pat_end
