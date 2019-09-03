def sqrtss1 : instruction :=
  definst "sqrtss" $ do
    pattern fun (v_3084 : reg (bv 128)) (v_3085 : reg (bv 128)) => do
      v_6767 <- getRegister v_3085;
      v_6769 <- getRegister v_3084;
      setRegister (lhs.of_reg v_3085) (concat (extract v_6767 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6769 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3079 : Mem) (v_3080 : reg (bv 128)) => do
      v_10278 <- getRegister v_3080;
      v_10280 <- evaluateAddress v_3079;
      v_10281 <- load v_10280 4;
      setRegister (lhs.of_reg v_3080) (concat (extract v_10278 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_10281));
      pure ()
    pat_end
