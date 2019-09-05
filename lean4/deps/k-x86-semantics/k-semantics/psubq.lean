def psubq1 : instruction :=
  definst "psubq" $ do
    pattern fun (v_3162 : reg (bv 128)) (v_3163 : reg (bv 128)) => do
      v_8038 <- getRegister v_3163;
      v_8040 <- getRegister v_3162;
      setRegister (lhs.of_reg v_3163) (concat (sub (extract v_8038 0 64) (extract v_8040 0 64)) (sub (extract v_8038 64 128) (extract v_8040 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3159 : Mem) (v_3158 : reg (bv 128)) => do
      v_14513 <- getRegister v_3158;
      v_14515 <- evaluateAddress v_3159;
      v_14516 <- load v_14515 16;
      setRegister (lhs.of_reg v_3158) (concat (sub (extract v_14513 0 64) (extract v_14516 0 64)) (sub (extract v_14513 64 128) (extract v_14516 64 128)));
      pure ()
    pat_end
