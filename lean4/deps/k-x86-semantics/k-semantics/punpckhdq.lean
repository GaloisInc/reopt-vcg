def punpckhdq1 : instruction :=
  definst "punpckhdq" $ do
    pattern fun (v_3171 : reg (bv 128)) (v_3172 : reg (bv 128)) => do
      v_9083 <- getRegister v_3171;
      v_9085 <- getRegister v_3172;
      setRegister (lhs.of_reg v_3172) (concat (concat (extract v_9083 0 32) (extract v_9085 0 32)) (concat (extract v_9083 32 64) (extract v_9085 32 64)));
      pure ()
    pat_end;
    pattern fun (v_3166 : Mem) (v_3167 : reg (bv 128)) => do
      v_15970 <- evaluateAddress v_3166;
      v_15971 <- load v_15970 16;
      v_15973 <- getRegister v_3167;
      setRegister (lhs.of_reg v_3167) (concat (concat (extract v_15971 0 32) (extract v_15973 0 32)) (concat (extract v_15971 32 64) (extract v_15973 32 64)));
      pure ()
    pat_end
