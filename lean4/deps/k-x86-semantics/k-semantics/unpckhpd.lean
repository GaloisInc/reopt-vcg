def unpckhpd1 : instruction :=
  definst "unpckhpd" $ do
    pattern fun (v_2546 : reg (bv 128)) (v_2547 : reg (bv 128)) => do
      v_4775 <- getRegister v_2546;
      v_4777 <- getRegister v_2547;
      setRegister (lhs.of_reg v_2547) (concat (extract v_4775 0 64) (extract v_4777 0 64));
      pure ()
    pat_end;
    pattern fun (v_2539 : Mem) (v_2542 : reg (bv 128)) => do
      v_10340 <- evaluateAddress v_2539;
      v_10341 <- load v_10340 16;
      v_10343 <- getRegister v_2542;
      setRegister (lhs.of_reg v_2542) (concat (extract v_10341 0 64) (extract v_10343 0 64));
      pure ()
    pat_end
