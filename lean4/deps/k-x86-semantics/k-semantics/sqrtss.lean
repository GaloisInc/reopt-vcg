def sqrtss1 : instruction :=
  definst "sqrtss" $ do
    pattern fun (v_3175 : reg (bv 128)) (v_3176 : reg (bv 128)) => do
      v_5513 <- getRegister v_3176;
      v_5515 <- getRegister v_3175;
      setRegister (lhs.of_reg v_3176) (concat (extract v_5513 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5515 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3171 : Mem) (v_3172 : reg (bv 128)) => do
      v_8566 <- getRegister v_3172;
      v_8568 <- evaluateAddress v_3171;
      v_8569 <- load v_8568 4;
      setRegister (lhs.of_reg v_3172) (concat (extract v_8566 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_8569));
      pure ()
    pat_end
