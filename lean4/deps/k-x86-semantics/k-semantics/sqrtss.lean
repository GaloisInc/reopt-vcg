def sqrtss1 : instruction :=
  definst "sqrtss" $ do
    pattern fun (v_3097 : reg (bv 128)) (v_3098 : reg (bv 128)) => do
      v_6763 <- getRegister v_3098;
      v_6765 <- getRegister v_3097;
      setRegister (lhs.of_reg v_3098) (concat (extract v_6763 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6765 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3092 : Mem) (v_3093 : reg (bv 128)) => do
      v_10300 <- getRegister v_3093;
      v_10302 <- evaluateAddress v_3092;
      v_10303 <- load v_10302 4;
      setRegister (lhs.of_reg v_3093) (concat (extract v_10300 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_10303));
      pure ()
    pat_end
