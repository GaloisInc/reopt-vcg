def punpckhqdq1 : instruction :=
  definst "punpckhqdq" $ do
    pattern fun (v_3243 : reg (bv 128)) (v_3244 : reg (bv 128)) => do
      v_8711 <- getRegister v_3243;
      v_8713 <- getRegister v_3244;
      setRegister (lhs.of_reg v_3244) (concat (extract v_8711 0 64) (extract v_8713 0 64));
      pure ()
    pat_end;
    pattern fun (v_3240 : Mem) (v_3239 : reg (bv 128)) => do
      v_15159 <- evaluateAddress v_3240;
      v_15160 <- load v_15159 16;
      v_15162 <- getRegister v_3239;
      setRegister (lhs.of_reg v_3239) (concat (extract v_15160 0 64) (extract v_15162 0 64));
      pure ()
    pat_end
