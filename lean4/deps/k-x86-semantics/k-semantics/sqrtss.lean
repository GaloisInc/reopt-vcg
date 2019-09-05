def sqrtss1 : instruction :=
  definst "sqrtss" $ do
    pattern fun (v_3147 : reg (bv 128)) (v_3148 : reg (bv 128)) => do
      v_6058 <- getRegister v_3148;
      v_6060 <- getRegister v_3147;
      setRegister (lhs.of_reg v_3148) (concat (extract v_6058 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6060 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3144 : Mem) (v_3143 : reg (bv 128)) => do
      v_9173 <- getRegister v_3143;
      v_9175 <- evaluateAddress v_3144;
      v_9176 <- load v_9175 4;
      setRegister (lhs.of_reg v_3143) (concat (extract v_9173 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_9176));
      pure ()
    pat_end
