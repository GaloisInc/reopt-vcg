def vsqrtss1 : instruction :=
  definst "vsqrtss" $ do
    pattern fun (v_2350 : reg (bv 128)) (v_2351 : reg (bv 128)) (v_2352 : reg (bv 128)) => do
      v_3191 <- getRegister v_2351;
      v_3193 <- getRegister v_2350;
      setRegister (lhs.of_reg v_2352) (concat (extract v_3191 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_3193 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2345 : Mem) (v_2346 : reg (bv 128)) (v_2347 : reg (bv 128)) => do
      v_6493 <- getRegister v_2346;
      v_6495 <- evaluateAddress v_2345;
      v_6496 <- load v_6495 4;
      setRegister (lhs.of_reg v_2347) (concat (extract v_6493 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_6496));
      pure ()
    pat_end
