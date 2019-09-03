def punpckldq1 : instruction :=
  definst "punpckldq" $ do
    pattern fun (v_3207 : reg (bv 128)) (v_3208 : reg (bv 128)) => do
      v_9167 <- getRegister v_3207;
      v_9169 <- getRegister v_3208;
      setRegister (lhs.of_reg v_3208) (concat (concat (extract v_9167 64 96) (extract v_9169 64 96)) (concat (extract v_9167 96 128) (extract v_9169 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3202 : Mem) (v_3203 : reg (bv 128)) => do
      v_16042 <- evaluateAddress v_3202;
      v_16043 <- load v_16042 16;
      v_16045 <- getRegister v_3203;
      setRegister (lhs.of_reg v_3203) (concat (concat (extract v_16043 64 96) (extract v_16045 64 96)) (concat (extract v_16043 96 128) (extract v_16045 96 128)));
      pure ()
    pat_end
