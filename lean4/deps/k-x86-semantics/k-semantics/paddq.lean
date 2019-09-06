def paddq1 : instruction :=
  definst "paddq" $ do
    pattern fun (v_3217 : reg (bv 128)) (v_3218 : reg (bv 128)) => do
      v_5737 <- getRegister v_3218;
      v_5739 <- getRegister v_3217;
      setRegister (lhs.of_reg v_3218) (concat (add (extract v_5737 0 64) (extract v_5739 0 64)) (add (extract v_5737 64 128) (extract v_5739 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3213 : Mem) (v_3214 : reg (bv 128)) => do
      v_9666 <- getRegister v_3214;
      v_9668 <- evaluateAddress v_3213;
      v_9669 <- load v_9668 16;
      setRegister (lhs.of_reg v_3214) (concat (add (extract v_9666 0 64) (extract v_9669 0 64)) (add (extract v_9666 64 128) (extract v_9669 64 128)));
      pure ()
    pat_end
