def movmskpd1 : instruction :=
  definst "movmskpd" $ do
    pattern fun (v_2602 : reg (bv 128)) (v_2603 : reg (bv 32)) => do
      v_4021 <- getRegister v_2602;
      setRegister (lhs.of_reg v_2603) (concat (expression.bv_nat 30 0) (concat (extract v_4021 0 1) (extract v_4021 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2608 : reg (bv 128)) (v_2607 : reg (bv 64)) => do
      v_4027 <- getRegister v_2608;
      setRegister (lhs.of_reg v_2607) (concat (expression.bv_nat 62 0) (concat (extract v_4027 0 1) (extract v_4027 64 65)));
      pure ()
    pat_end
