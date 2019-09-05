def paddq1 : instruction :=
  definst "paddq" $ do
    pattern fun (v_3192 : reg (bv 128)) (v_3193 : reg (bv 128)) => do
      v_5710 <- getRegister v_3193;
      v_5712 <- getRegister v_3192;
      setRegister (lhs.of_reg v_3193) (concat (add (extract v_5710 0 64) (extract v_5712 0 64)) (add (extract v_5710 64 128) (extract v_5712 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3187 : Mem) (v_3188 : reg (bv 128)) => do
      v_9639 <- getRegister v_3188;
      v_9641 <- evaluateAddress v_3187;
      v_9642 <- load v_9641 16;
      setRegister (lhs.of_reg v_3188) (concat (add (extract v_9639 0 64) (extract v_9642 0 64)) (add (extract v_9639 64 128) (extract v_9642 64 128)));
      pure ()
    pat_end
