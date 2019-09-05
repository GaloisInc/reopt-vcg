def unpckhpd1 : instruction :=
  definst "unpckhpd" $ do
    pattern fun (v_2597 : reg (bv 128)) (v_2598 : reg (bv 128)) => do
      v_4736 <- getRegister v_2597;
      v_4738 <- getRegister v_2598;
      setRegister (lhs.of_reg v_2598) (concat (extract v_4736 0 64) (extract v_4738 0 64));
      pure ()
    pat_end;
    pattern fun (v_2592 : Mem) (v_2593 : reg (bv 128)) => do
      v_9058 <- evaluateAddress v_2592;
      v_9059 <- load v_9058 16;
      v_9061 <- getRegister v_2593;
      setRegister (lhs.of_reg v_2593) (concat (extract v_9059 0 64) (extract v_9061 0 64));
      pure ()
    pat_end
