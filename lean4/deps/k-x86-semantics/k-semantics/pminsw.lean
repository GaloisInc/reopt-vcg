def pminsw1 : instruction :=
  definst "pminsw" $ do
    pattern fun (v_2620 : reg (bv 128)) (v_2621 : reg (bv 128)) => do
      v_5196 <- getRegister v_2621;
      v_5197 <- eval (extract v_5196 0 16);
      v_5198 <- getRegister v_2620;
      v_5199 <- eval (extract v_5198 0 16);
      v_5202 <- eval (extract v_5196 16 32);
      v_5203 <- eval (extract v_5198 16 32);
      v_5206 <- eval (extract v_5196 32 48);
      v_5207 <- eval (extract v_5198 32 48);
      v_5210 <- eval (extract v_5196 48 64);
      v_5211 <- eval (extract v_5198 48 64);
      v_5214 <- eval (extract v_5196 64 80);
      v_5215 <- eval (extract v_5198 64 80);
      v_5218 <- eval (extract v_5196 80 96);
      v_5219 <- eval (extract v_5198 80 96);
      v_5222 <- eval (extract v_5196 96 112);
      v_5223 <- eval (extract v_5198 96 112);
      v_5226 <- eval (extract v_5196 112 128);
      v_5227 <- eval (extract v_5198 112 128);
      setRegister (lhs.of_reg v_2621) (concat (mux (slt v_5197 v_5199) v_5197 v_5199) (concat (mux (slt v_5202 v_5203) v_5202 v_5203) (concat (mux (slt v_5206 v_5207) v_5206 v_5207) (concat (mux (slt v_5210 v_5211) v_5210 v_5211) (concat (mux (slt v_5214 v_5215) v_5214 v_5215) (concat (mux (slt v_5218 v_5219) v_5218 v_5219) (concat (mux (slt v_5222 v_5223) v_5222 v_5223) (mux (slt v_5226 v_5227) v_5226 v_5227))))))));
      pure ()
    pat_end;
    pattern fun (v_2615 : Mem) (v_2616 : reg (bv 128)) => do
      v_12575 <- getRegister v_2616;
      v_12576 <- eval (extract v_12575 0 16);
      v_12577 <- evaluateAddress v_2615;
      v_12578 <- load v_12577 16;
      v_12579 <- eval (extract v_12578 0 16);
      v_12582 <- eval (extract v_12575 16 32);
      v_12583 <- eval (extract v_12578 16 32);
      v_12586 <- eval (extract v_12575 32 48);
      v_12587 <- eval (extract v_12578 32 48);
      v_12590 <- eval (extract v_12575 48 64);
      v_12591 <- eval (extract v_12578 48 64);
      v_12594 <- eval (extract v_12575 64 80);
      v_12595 <- eval (extract v_12578 64 80);
      v_12598 <- eval (extract v_12575 80 96);
      v_12599 <- eval (extract v_12578 80 96);
      v_12602 <- eval (extract v_12575 96 112);
      v_12603 <- eval (extract v_12578 96 112);
      v_12606 <- eval (extract v_12575 112 128);
      v_12607 <- eval (extract v_12578 112 128);
      setRegister (lhs.of_reg v_2616) (concat (mux (slt v_12576 v_12579) v_12576 v_12579) (concat (mux (slt v_12582 v_12583) v_12582 v_12583) (concat (mux (slt v_12586 v_12587) v_12586 v_12587) (concat (mux (slt v_12590 v_12591) v_12590 v_12591) (concat (mux (slt v_12594 v_12595) v_12594 v_12595) (concat (mux (slt v_12598 v_12599) v_12598 v_12599) (concat (mux (slt v_12602 v_12603) v_12602 v_12603) (mux (slt v_12606 v_12607) v_12606 v_12607))))))));
      pure ()
    pat_end
