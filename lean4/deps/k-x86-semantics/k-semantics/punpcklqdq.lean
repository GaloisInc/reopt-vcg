def punpcklqdq1 : instruction :=
  definst "punpcklqdq" $ do
    pattern fun (v_3307 : reg (bv 128)) (v_3308 : reg (bv 128)) => do
      v_8822 <- getRegister v_3307;
      v_8824 <- getRegister v_3308;
      setRegister (lhs.of_reg v_3308) (concat (extract v_8822 64 128) (extract v_8824 64 128));
      pure ()
    pat_end;
    pattern fun (v_3303 : Mem) (v_3304 : reg (bv 128)) => do
      v_15207 <- evaluateAddress v_3303;
      v_15208 <- load v_15207 16;
      v_15210 <- getRegister v_3304;
      setRegister (lhs.of_reg v_3304) (concat (extract v_15208 64 128) (extract v_15210 64 128));
      pure ()
    pat_end
